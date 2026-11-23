module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
public import Development.WeilBound.CoreStatements.SesquilinearFractions.DTransUnit
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle015
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle042
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle076
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChowDegree
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle024
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle005
import Mathlib.Algebra.MvPolynomial.Nilpotent
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle023
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle049
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle009
public import Mathlib.RingTheory.RingHom.Etale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle140
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
public import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.CompanionTheory.Relay.padic_norm_transition_det_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (I : Type) [Fintype I] [DecidableEq I] (x e : I → D.La) (T : Matrix I I E) (ℓ : Nat.Primes), IsLocBasis (𝓞 E) ℓ x → IsLocBasis (𝓞 E) ℓ e → IsTransition D x e T → ∀ j : E →+* ℂ_[ℓ], ‖j T.det‖ = 1 := by
  first | exact @PositivityTheory.Xgf.padic_norm_transition_det_one | exact PositivityTheory.Xgf.padic_norm_transition_det_one
end

section

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Short

open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial

theorem mahlerDefect_eq_sum {n e δ : ℕ} (h : HermNorm n) {Z : ProjCycle ℂ n}
    {f : MvPolynomial (Fin (e + 1) × Fin n) ℂ} (hd : IsChowCycleData Z e δ f) :
    ∃ (c : ℂ) (g : Ideal (MvPolynomial (Fin n) ℂ) → MvPolynomial (Fin (e + 1) × Fin n) ℂ)
      (d : Ideal (MvPolynomial (Fin n) ℂ) → ℕ),
      (∀ W ∈ Z.support, IsChowForm W (e + 1) (g W) ∧ IsMultiHomog (d W) (g W)) ∧
      ∀ u : Fin n → ℂ, IsAdmissible Z u →
        mahlerDefect h e Z f u = Real.log ‖c‖ + ∑ W ∈ Z.support, (Z W : ℝ) *
          (mahler h e (specFirst (g W) u) - coneIntegral h W e (fsLog h u)) := by
  obtain ⟨c, hc, g, hg, hf⟩ := hd.chow
  have hf0 : C c * ∏ W ∈ Z.support, g W ^ Z W ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr hc)
      (Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hg W hW).1)
  have hhom : IsMultiHomog δ (C c * ∏ W ∈ Z.support, g W ^ Z W) := hf ▸ hd.homog
  obtain ⟨d, hdW, -⟩ := exists_degrees_of_chowFormCycle (Nat.succ_pos e) Z c g hg hhom hf0
  refine ⟨c, g, d, fun W hW => ⟨hg W hW, hdW W hW⟩, fun u hu => ?_⟩
  have hspec : specFirst f u = C c * ∏ W ∈ Z.support, specFirst (g W) u ^ Z W := by
    rw [hf]
    simp only [specFirst, map_mul, map_prod, map_pow, bind₁_C_right]
  have hq : ∀ W ∈ Z.support, specFirst (g W) u ≠ 0 ∧ IsMultiHomog (d W) (specFirst (g W) u) :=
    fun W hW => ⟨SpecFirstNe.full ℂ n e W (g W) u (hd.prime W hW) (hg W hW) (hu W hW),
      SpecFirstHomog.proof n e (d W) (g W) u (hdW W hW)⟩
  rw [mahlerDefect, hspec, GlobalTheory.T.mahler_measure_of_product n e h Z.support (fun W => specFirst (g W) u) d (fun W => Z W) c hc hq,
    cycleIntegral]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

theorem defectConstDim (e : ℕ) : DefectConstDim e := by
  intro n δ h Z f u u' hd hu hu'
  obtain ⟨c, g, d, hg, hsum⟩ := mahlerDefect_eq_sum h hd
  have hW : ∀ W ∈ Z.support, (Z W : ℝ) * (mahler h e (specFirst (g W) u) - coneIntegral h W e (fsLog h u)) =
      (Z W : ℝ) * (mahler h e (specFirst (g W) u') - coneIntegral h W e (fsLog h u')) := fun W hW => by
    have := GlobalTheory.T.mahler_minus_cone_integral_indep n e (d W) h W (g W) u u' (hd.prime W hW) (hg W hW).1 (hg W hW).2 (hu W hW)
      (hu' W hW)
    rw [this]
  rw [hsum u hu, hsum u' hu', Finset.sum_congr rfl hW]

theorem mahlerSection : GroundTheory.Heights₂.Heights.MahlerSection.Statement := by
  intro n e δ h Z f u hp hc hm ha
  exact GroundTheory.Heights₂.Heights.AutoClose.MahlerSectionOfConst e (defectConstDim e) n δ h Z f u ⟨hp, hc, hm⟩ ha

end GlobalTheory.CompanionTheory.Ar.Short
end

section

namespace GlobalTheory.CompanionTheory.CommAlg.VerticalDivisors

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem verticalDivisorsCommute : VerticalDivisorsCommute.Statement.{0} :=
  VerticalDivisorsCommute.proof GlobalTheory.T.cut_effective_divisor Representative.full
    IntNumAddFirst.full DivCycleFiniteSupport.full MinimalPrimeMultiHomog.full
    SupSpanMultiHomog.full SpecialQuotDim.full SpecialIdealCorresp.full SpecialIdealMultiHomog.full
    DimStrictDrop.full

end GlobalTheory.CompanionTheory.CommAlg.VerticalDivisors
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.CommAlg.OrderEtale

theorem formallyUnramified_fractionRing (k K : Type) [CommRing k] [IsDomain k] [CharZero k]
    [Module.Finite ℤ k] [Field K] [Algebra k K] [IsFractionRing k K] [Algebra ℤ K] :
    Algebra.FormallyUnramified ℤ K := by
  have hinj : Function.Injective (algebraMap k K) := IsFractionRing.injective k K
  haveI : CharZero K := charZero_of_injective_algebraMap hinj
  letI : Algebra ℚ K := DivisionRing.toRatAlgebra
  haveI := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := ℚ) (A := K) (RingHom.ext_int _ _)
  haveI := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := k) (A := K) (RingHom.ext_int _ _)
  haveI : Algebra.IsIntegral ℤ k := Algebra.IsIntegral.of_finite ℤ k
  have hint : ∀ a : k, IsIntegral ℚ (algebraMap k K a) := fun a =>
    IsIntegral.tower_top (A := ℚ)
      ((Algebra.IsIntegral.isIntegral (R := ℤ) a).algebraMap (B := K))
  haveI : Algebra.IsAlgebraic ℚ K := by
    constructor
    intro x
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := k) x
    rw [div_eq_mul_inv]
    have hb : IsIntegral ℚ (algebraMap k K b)⁻¹ :=
      (IsAlgebraic.inv_iff.mpr (hint b).isAlgebraic).isIntegral
    exact ((hint a).mul hb).isAlgebraic
  haveI : Algebra.FormallyUnramified ℚ K := Algebra.FormallyUnramified.of_isSeparable ℚ K
  haveI : Algebra.FormallyUnramified ℤ ℚ := Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors ℤ)
  exact Algebra.FormallyUnramified.comp ℤ ℚ K

theorem isUnramifiedAt_bot (k : Type) [CommRing k] [IsDomain k] [CharZero k]
    [Module.Finite ℤ k] : Algebra.IsUnramifiedAt ℤ (⊥ : Ideal k) := by
  have hM : (⊥ : Ideal k).primeCompl = nonZeroDivisors k := by
    ext x
    simp [Ideal.mem_primeCompl_iff, mem_nonZeroDivisors_iff_ne_zero]
  haveI : IsFractionRing k (Localization.AtPrime (⊥ : Ideal k)) := by
    unfold IsFractionRing
    rw [← hM]
    infer_instance
  letI : Field (Localization.AtPrime (⊥ : Ideal k)) := IsFractionRing.toField k
  exact formallyUnramified_fractionRing k (Localization.AtPrime (⊥ : Ideal k))

theorem exists_etale_away (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] :
    ∃ N : ℕ, N ≠ 0 ∧ (Int.castRingHom (Localization.Away (N : k))).Etale := by
  have hU : IsOpen (Algebra.unramifiedLocus ℤ k) := Algebra.isOpen_unramifiedLocus
  have hbot : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k) ∈ Algebra.unramifiedLocus ℤ k :=
    isUnramifiedAt_bot k
  obtain ⟨V, ⟨f, rfl⟩, hfV, hVU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hbot hU
  have hf0 : f ≠ 0 := by
    intro h
    simp [h] at hfV
  have hint : Algebra.IsIntegral ℤ k := Algebra.IsIntegral.of_finite ℤ k
  have hne : Ideal.comap (algebraMap ℤ k) (Ideal.span {f}) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hf0 (Ideal.subset_span rfl) (Algebra.IsIntegral.isIntegral f)
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Ideal.mem_comap, Ideal.mem_span_singleton, eq_intCast] at hm
  have hmN : (m : k) ∣ ((m.natAbs : ℤ) : k) := map_dvd (Int.castRingHom k) (Int.dvd_natAbs.mpr dvd_rfl)
  have hfN : f ∣ ((m.natAbs : ℕ) : k) := by
    have := hm.trans hmN
    simpa using this
  obtain ⟨g, hg⟩ := hfN
  refine ⟨m.natAbs, Int.natAbs_ne_zero.mpr hm0, ?_⟩
  have hS : Algebra.FormallyUnramified ℤ (Localization.Away ((m.natAbs : ℕ) : k)) := by
    rw [← Algebra.basicOpen_subset_unramifiedLocus_iff]
    refine subset_trans ?_ hVU
    rw [hg]
    exact PrimeSpectrum.basicOpen_mul_le_left f g
  have hfree : Module.Free ℤ k := Module.free_of_finite_type_torsion_free'
  have hflat : Module.Flat ℤ (Localization.Away ((m.natAbs : ℕ) : k)) := by
    have := IsLocalization.flat (Localization.Away ((m.natAbs : ℕ) : k))
      (Submonoid.powers ((m.natAbs : ℕ) : k))
    exact Module.Flat.trans ℤ k _
  have hfp : Algebra.FinitePresentation ℤ (Localization.Away ((m.natAbs : ℕ) : k)) := by
    have : Algebra.FinitePresentation ℤ k := Algebra.FinitePresentation.of_finiteType.mp inferInstance
    have := IsLocalization.Away.finitePresentation (S := Localization.Away ((m.natAbs : ℕ) : k))
      ((m.natAbs : ℕ) : k)
    exact Algebra.FinitePresentation.trans ℤ k _
  have hE : Algebra.Etale ℤ (Localization.Away ((m.natAbs : ℕ) : k)) :=
    Algebra.Etale.of_formallyUnramified_of_flat
  have h2 : Int.castRingHom (Localization.Away ((m.natAbs : ℕ) : k)) =
      algebraMap ℤ (Localization.Away ((m.natAbs : ℕ) : k)) := RingHom.ext_int _ _
  rw [h2, RingHom.etale_algebraMap]
  exact hE

end GlobalTheory.CompanionTheory.CommAlg.OrderEtale
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.EtaleCoord

theorem etale_of_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S)
    (g : S →+* T) (hf : f.Etale) (h : (g.comp f).Etale) : g.Etale := by
  algebraize [f, g, g.comp f]
  exact Algebra.Etale.of_restrictScalars R S T

theorem etale_eval₂Hom_iff_int : ∀ (k A : Type) [CommRing k] [CommRing A] (N : ℕ), (Int.castRingHom (Localization.Away (N : k))).Etale → ∀ (φ : k →+* A), IsUnit (N : A) → ∀ (D : ℕ) (x : Fin D → A), (MvPolynomial.eval₂Hom φ x).Etale ↔ (MvPolynomial.eval₂Hom (Int.castRingHom A) x).Etale := by
  intro k A _ _ N hN φ hu D x
  let ι : k →+* Localization.Away (N : k) := algebraMap k _
  have hφN : IsUnit (φ (N : k)) := by simpa using hu
  let ψ : Localization.Away (N : k) →+* A := IsLocalization.Away.lift (N : k) hφN
  have hψ : ψ.comp ι = φ := by
    ext a
    simp [ψ, ι]
  have hι : ι.Etale := by
    rw [RingHom.etale_algebraMap]
    exact Algebra.Etale.of_isLocalizationAway (N : k)
  have ha : (MvPolynomial.map (σ := Fin D) ι).Etale := etale_mvPolynomial_map_of_etale ι hι
  have hb : (MvPolynomial.map (σ := Fin D) (Int.castRingHom (Localization.Away (N : k)))).Etale :=
    etale_mvPolynomial_map_of_etale _ hN
  let Θ := MvPolynomial.eval₂Hom ψ x
  have e1 : MvPolynomial.eval₂Hom φ x = Θ.comp (MvPolynomial.map ι) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [Θ, ← hψ]
    · intro j
      simp [Θ]
  have e2 : MvPolynomial.eval₂Hom (Int.castRingHom A) x =
      Θ.comp (MvPolynomial.map (Int.castRingHom (Localization.Away (N : k)))) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [Θ]
    · intro j
      simp [Θ]
  rw [e1, e2]
  exact ⟨fun h => RingHom.Etale.stableUnderComposition _ _ hb (etale_of_comp _ _ ha h),
    fun h => RingHom.Etale.stableUnderComposition _ _ ha (etale_of_comp _ _ hb h)⟩

end GlobalTheory.CompanionTheory.Ar.EtaleCoord
end
