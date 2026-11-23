module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle418
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle419
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle420
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle246
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle429
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle384
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalMapSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle403
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle141
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle150
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle011
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle006
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle003
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsNormalChartsOfCoveringCharts
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle004
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle421
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle173

@[expose] public section

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.admA_admB_inert_band_tab : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.admA L (tab L X tf C) C ∧ TwistedPlaces.admB L (tab L X tf C) C ∧ TwistedPlaces.MediumInertPrimeLengthBound L (tab L X tf C) C ∧ TwistedPlaces.SmallInertPrimeSmallOrderLengthBound L (tab L X tf C) C ∧ TwistedPlaces.BandPlaceWeightApproximation L (tab L X tf C) C := by
  first | exact @GlobalTheory.NLink.localBoundTableAllPrimes_rowsAndBand | exact GlobalTheory.NLink.localBoundTableAllPrimes_rowsAndBand | (intros; apply GlobalTheory.NLink.localBoundTableAllPrimes_rowsAndBand <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.admissible_table_of_local_bounds : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → (∀ i, TwistedPlaces.TwLoc D i → (D.nd.l i ∈ D.host.small ∨ D.nd.l i = 3) → ∀ π ∈ D.nd.Zgood i, Bd X.ρ i π (TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i)) → TwistedPlaces.ArchimedeanSignatureMatching L (tab L X tf C) := by
  first | exact @GlobalTheory.NLink.admissible_table_of_conclusion | exact GlobalTheory.NLink.admissible_table_of_conclusion | (intros; apply GlobalTheory.NLink.admissible_table_of_conclusion <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.ramifiedPrimeLengthBound_and_generatorPrimeEtaBound_tab : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.RamifiedPrimeLengthBound L (tab L X tf C) C ∧ TwistedPlaces.GeneratorPrimeEtaBound L (tab L X tf C) C := by
  first | exact @GlobalTheory.NLink.localBoundTableAllPrimes_ramified_typePrimes | exact GlobalTheory.NLink.localBoundTableAllPrimes_ramified_typePrimes | (intros; apply GlobalTheory.NLink.localBoundTableAllPrimes_ramified_typePrimes <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.localBoundTableAllPrimes_sizeConditionSix : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.adm6 L (tab L X tf C) := by
  first | exact @GlobalTheory.NLink.adm6_tab | exact GlobalTheory.NLink.adm6_tab | (intros; apply GlobalTheory.NLink.adm6_tab <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.sizeConditions_mono : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C C' : ℝ), C ≤ C' → 0 ≤ C' → (StarF L X.ρ C → StarF L X.ρ C') ∧ (StarH L C → StarH L C') ∧ (KillingConditions.BBLe L X C → KillingConditions.BBLe L X C') ∧ (TwistedPlaces.ParametersPolynomiallyBounded L C P → TwistedPlaces.ParametersPolynomiallyBounded L C' P) := by
  first | exact @GlobalTheory.NLinkMono.main | exact GlobalTheory.NLinkMono.main | (intros; apply GlobalTheory.NLinkMono.main <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.localBoundTableFromData_bandCondition : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ), KillingConditions.DataAD L HW X R → R.Le C → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → TwistedPlaces.BandPlaceWeightApproximation L (tabX L X) C := by
  first | exact @GlobalTheory.NBand.bandPlaceWeightApproximation_tabX | exact GlobalTheory.NBand.bandPlaceWeightApproximation_tabX | (intros; apply GlobalTheory.NBand.bandPlaceWeightApproximation_tabX <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.goodPointMultiplicityLeRank_proof : ∀ (D : D7) (L : SizeData₂ D), SumRepresentations.Conclusion42 D → SumRepresentations.ConclusionZ D → Rows.IsotInternal D.what₂ → KillingConditions.LocalisationUniqueness D → MultLe L := by
  first | exact @GlobalTheory.NLink.multLe_of_rank | exact GlobalTheory.NLink.multLe_of_rank | (intros; apply GlobalTheory.NLink.multLe_of_rank <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.PhiDec

theorem phi_dec : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ a : AA K LL, ∃ c : Fin l → AA K LL, a = ∑ j : Fin l, (fun _ => ((1 : PowerSeries ↥(OL LL)) + PowerSeries.X) ^ (j : ℕ) : AA K LL) * W.φA (c j) := by
  intro D HW l _ K s LL h W a
  obtain ⟨χ, -, hφ, -⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h
  obtain ⟨hdvr, hcomp, hl0, hlu, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  choose z hz using fun i : Let K => (GlobalTheory.Cyc.phi_free l ↥(OL LL) hl0 hlu (a i)).exists
  refine ⟨fun j i => z (i + 1) j, ?_⟩
  funext i
  rw [Finset.sum_apply]
  have hi : a i = a (i - 1 + 1) := by rw [sub_add_cancel]
  rw [hi, hz]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.mul_apply, LocWach.φA, letφ, AlgHom.pi_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply]
  show _ = _ * ((HW l).W K s LL h).φ₀ _
  rw [hφ]

end GlobalTheory.NL.PhiDec
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PSer TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PSer

open GlobalTheory.MemLoc GlobalTheory.MemLoc.TiedTheta

theorem theta_fil_acris : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    ∃ (S : Subring P.R.BdR) (θ : ↥S →+* ℂ_[l]) (Θ : Formalism.Per.Acris l →+* ℂ_[l]),
      (∀ x, x ∈ S ↔ x ∈ Fil P 0) ∧ (∀ x : ↥S, θ x = 0 ↔ (x : P.R.BdR) ∈ Fil P 1) ∧
      (∀ c : ℚ_[l], ∃ hm, θ ⟨algebraMap ℚ_[l] P.R.BdR c, hm⟩ = algebraMap ℚ_[l] ℂ_[l] c) ∧
      (∀ a, ‖Θ a‖ ≤ 1) ∧
      (∀ z : Formalism.Per.Fl l, Θ (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (Formalism.Per.tm z)) = sh z) ∧
      ∀ a : Formalism.Per.Acris l, ∃ hm, θ ⟨P.ιB (T.eB.symm (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) a)), hm⟩ = Θ a := by
  intro l _ P AI T
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  let S : Subring P.R.BdR := (algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l)).range.comap T.eD.toRingHom
  have hS : ∀ x, x ∈ S ↔ ∃ y : Formalism.Per.BdRp l, T.eD x = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) y := by
    intro x
    change (∃ y, _ = T.eD x) ↔ _
    exact exists_congr fun y => eq_comm
  have hF0 : ∀ x, x ∈ S ↔ x ∈ Fil P 0 := by
    intro x
    rw [hS]
    change _ ↔ x ∈ (P.PD (botExt l)).Fil 0
    rw [T.fil]
    constructor
    · rintro ⟨y, hy⟩
      rw [hy]
      exact TiedUnif.alg_mem_FilD_zero y
    · intro hx
      obtain ⟨y, hy⟩ := exists_of_mem_FilD_zero hx
      exact ⟨y, hy⟩
  let θ : ↥S →+* ℂ_[l] :=
    { toFun := fun x => thetaExt (T.eD x)
      map_one' := by
        change thetaExt (T.eD 1) = 1
        rw [map_one, ← map_one (algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l)), thetaExt_alg, map_one]
      map_mul' := fun x y => by
        obtain ⟨u, hu⟩ := (hS x).1 x.2
        obtain ⟨v, hv⟩ := (hS y).1 y.2
        change thetaExt (T.eD ((x : P.R.BdR) * y)) = thetaExt (T.eD x) * thetaExt (T.eD y)
        rw [map_mul, hu, hv, ← map_mul, thetaExt_alg, thetaExt_alg, thetaExt_alg, map_mul]
      map_zero' := by
        change thetaExt (T.eD 0) = 0
        rw [map_zero, ← map_zero (algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l)), thetaExt_alg, map_zero]
      map_add' := fun x y => by
        obtain ⟨u, hu⟩ := (hS x).1 x.2
        obtain ⟨v, hv⟩ := (hS y).1 y.2
        change thetaExt (T.eD ((x : P.R.BdR) + y)) = thetaExt (T.eD x) + thetaExt (T.eD y)
        rw [map_add (f := _), hu, hv, ← map_add (f := _), thetaExt_alg, thetaExt_alg, thetaExt_alg, map_add (f := _)] }
  have hθ : ∀ (x : ↥S) (y : Formalism.Per.BdRp l), T.eD x = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) y →
      θ x = Formalism.Per.θD l y := by
    intro x y h
    change thetaExt (T.eD x) = _
    rw [h, thetaExt_alg]
  let Θ : Formalism.Per.Acris l →+* ℂ_[l] := (Formalism.Per.θD l).comp C.j
  refine ⟨S, θ, Θ, hF0, fun x => ?_, fun c => ?_, fun a => FundOnto.norm_theta_j_le C a, fun z => ?_,
    fun a => ?_⟩
  · obtain ⟨u, hu⟩ := (hS x).1 x.2
    change θ x = 0 ↔ (x : P.R.BdR) ∈ (P.PD (botExt l)).Fil 1
    rw [T.fil, hu, hθ x u hu, (thetaD_props l).2.1]
    exact ((filD_laws l).2.2.2.2.2.2 1 u).symm
  · have e : algebraMap ℚ_[l] P.R.BdR c = algebraMap (Om l) P.R.BdR (algebraMap ℚ_[l] (Om l) c) :=
      IsScalarTower.algebraMap_apply _ _ _ _
    obtain ⟨y, hy, hy'⟩ := T.om (algebraMap ℚ_[l] (Om l) c)
    have hm : algebraMap ℚ_[l] P.R.BdR c ∈ S := by
      rw [hS, e]
      exact ⟨y, hy⟩
    refine ⟨hm, ?_⟩
    rw [hθ ⟨_, hm⟩ y (by rw [← hy]; exact congrArg T.eD e), hy']
    rfl
  · change Formalism.Per.θD l (C.j _) = _
    rw [FundOnto.theta_j_alg, FundOnto.theta_tm]
    rfl
  · have hm : P.ιB (T.eB.symm (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) a)) ∈ S := by
      rw [hS, hC.ι, RingEquiv.apply_symm_apply, C.ι_j]
      exact ⟨_, rfl⟩
    refine ⟨hm, hθ ⟨_, hm⟩ (C.j a) ?_⟩
    change T.eD (P.ιB _) = _
    rw [hC.ι, RingEquiv.apply_symm_apply, C.ι_j]

end GlobalTheory.PSer
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts GlobalTheory.GoodTransfer

namespace GlobalTheory.ChartIntegral

open GlobalTheory.Reg.NormalCharts GlobalTheory.PlaceCompletion

theorem exists_quotient_of_bounded (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero O] [CommRing A] [IsDomain A]
    [Algebra O A] [Algebra.FiniteType O A] [IsIntegrallyClosed A]
    (hOA : Function.Injective (algebraMap O A)) (e : A) (he : e ≠ 0) (f : FractionRing A)
    (hf : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
      [Module.Finite O V] (φ : A →+* V), (∀ a, φ (algebraMap O A a) = algebraMap O V a) → φ e ≠ 0 →
      ∀ a b : A, f * algebraMap A _ b = algebraMap A _ a → φ b ≠ 0 → φ b ∣ φ a) :
    ∃ x s : A, s - 1 ∈ Ideal.map (algebraMap O A) (IsLocalRing.maximalIdeal O) ∧
      f * algebraMap A _ s = algebraMap A _ x := by
  have hid : Function.Injective (algebraMap O O) := fun _ _ h => h
  have : IsLocalHom (algebraMap O O) := ⟨fun _ h => h⟩
  obtain ⟨s, hs, hint⟩ := GlobalTheory.isIntegral_mul_of_bounded_at_points O O hid
    (GlobalTheory.exists_integral_point_of_complete_case
      (fun O B _ _ _ _ _ _ _ _ _ _ M hM hsp e he => GlobalTheory.exists_integral_point_through O B M hM hsp e he)
      O O hid) A (FractionRing A) hOA e he f
    (fun V _ _ _ _ _ φ hφ => hf V φ (fun a => RingHom.congr_fun hφ a))
  obtain ⟨x, hx⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  exact ⟨x, s, hs, by rw [hx, _root_.mul_comm]⟩

theorem integral_of_integral_at_algebraic_points :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (la : HeightOneSpectrum (𝓞 K)) (gens : Finset Ω) (e : Ω), Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) = ⊤ → e ≠ 0 → e ∈ Subring.closure (Set.range ((algebraMap K Ω).comp (la.valuation K).valuationSubring.subtype) ∪ (gens : Set Ω)) → Algebra.Smooth K (Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))) → ∀ r : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), (∀ (T : CDVR) (io : K →+* T.Fr) (n : ℕ), OverLa la T.V io n → T.FinRes → ∀ ψ : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) →+* T.Fr, (∀ k : K, ψ (algebraMap K _ k) = io k) → (∀ g : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), (g : Ω) ∈ gens → InV T (ψ g)) → InV T (ψ r)) → ∀ (T : CDVR) (io : K →+* T.Fr) (n : ℕ), OverLa la T.V io n → ∀ ψ : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) →+* T.Fr, (∀ k : K, ψ (algebraMap K _ k) = io k) → (∀ g : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), (g : Ω) ∈ gens → InV T (ψ g)) → InV T (ψ r) := by
  intro K Ω _ _ _ _ la gens e hgen he hemem hsm r hr T io n ho ψ hψK hψg
  obtain ⟨T₀, io₀, hov, hfin, hinit⟩ := exists_initial_completion K la
  have hβ : ∀ a : (la.valuation K).valuationSubring,
      io₀ ((la.valuation K).valuationSubring.subtype a) ∈ Set.range (algebraMap T₀.V T₀.Fr) := fun a =>
    exists_algebraMap_eq_of_valV_le_one (by
      rw [valV_eq_pow_of_overLa hov]
      exact pow_le_one₀ zero_le a.2)
  obtain ⟨J, finJ, A, acr, adom, alg, α, hA, hK, hg, hcov⟩ :=
    GlobalTheory.exists_normal_charts_over_dvr K Ω T₀.V io₀ gens {e} hgen
      (fun e' he' => by
        obtain rfl := Finset.mem_singleton.1 he'
        refine ⟨he, Subring.closure_mono ?_ hemem⟩
        refine Set.union_subset_union_left _ ?_
        rintro _ ⟨a, rfl⟩
        exact ⟨_, hβ a, rfl⟩)
      (fun e' he' => by
        obtain rfl := Finset.mem_singleton.1 he'
        exact hsm)
  obtain ⟨g, χ, hloc, hχio, hχg, -⟩ := hinit T io n ho
  have hχg' : ∀ a, χ (algebraMap T₀.V T₀.Fr a) = algebraMap T.V T.Fr (g a) :=
    fun a => RingHom.congr_fun hχg a
  obtain ⟨j, φ, hφW, hφO, hφψ⟩ := hcov e (Finset.mem_singleton_self e) T.Fr (imageVal T.V T.Fr) χ ψ
    (fun k => (hψK k).trans (RingHom.congr_fun hχio k).symm)
    (fun a => (mem_imageVal _).2 ⟨g a, (hχg' a).symm⟩)
    (fun x hx => (mem_imageVal _).2 (hψg x hx))
  obtain ⟨φ', hφ'⟩ := exists_corestrict (V := T.V) φ fun x => (mem_imageVal _).1 (hφW x)
  have hc : ∀ a, φ' (algebraMap T₀.V (A j) a) = g a := fun a =>
    IsFractionRing.injective T.V T.Fr (by rw [hφ', hφO, hχg'])
  obtain ⟨hft, -, hic⟩ := hA j
  have hOA : Function.Injective (algebraMap T₀.V (A j)) := by
    intro a b hab
    apply IsFractionRing.injective T₀.V T₀.Fr
    apply χ.injective
    exact (hφO a).symm.trans ((congrArg φ hab).trans (hφO b))
  obtain ⟨eb, heb⟩ : α j e ∈ Set.range (algebraMap (A j) (FractionRing (A j))) := by
    refine (Subring.closure_le (t := (algebraMap (A j) (FractionRing (A j))).range.comap (α j))).2 ?_ hemem
    rintro x (⟨a, rfl⟩ | hx)
    · obtain ⟨x, hx⟩ := hβ a
      have := hK j ((la.valuation K).valuationSubring.subtype a) x 1 (by rw [map_one, _root_.mul_one, hx])
      rw [map_one, map_one, _root_.mul_one] at this
      exact ⟨_, this.symm⟩
    · exact hg j x hx
  have heb0 : eb ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, map_eq_zero] at heb
    exact he heb
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T₀.V
  obtain ⟨x, s, hs, hxs⟩ := exists_quotient_of_bounded T₀.V (A j) hOA eb heb0 (α j r) (by
    intro V _ _ _ _ _ ρ hρ h0 a b hab hb
    obtain ⟨hinj, hlocV, hcpl, hch, hfin'⟩ := GlobalTheory.dvr_finite_over_complete_dvr T₀.V V
    obtain ⟨χ', m, hm, hχ', hv⟩ := exists_ramification (K' := FractionRing V) (F := T₀.Fr)
      (algebraMap T₀.V V) hinj hlocV
    obtain ⟨ψ', hψ'⟩ := (GlobalTheory.Reg.openChart_regular_away K Ω T₀.V (A j) io₀ gens e (α j) eb ϖ hϖ he heb
      (hK j) (hg j)).2 (FractionRing V) ((algebraMap V (FractionRing V)).comp ρ) (by
        change algebraMap V (FractionRing V) (ρ _) ≠ 0
        rw [map_mul, hρ]
        simpa using mul_ne_zero ((map_ne_zero_iff _ hinj).2 hϖ.ne_zero) h0)
    replace hψ' : ∀ (r : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))) (x s : A j),
        α j r * algebraMap (A j) _ s = algebraMap (A j) _ x →
        ψ' r * algebraMap V _ (ρ s) = algebraMap V _ (ρ x) := hψ'
    let T' : CDVR := { V := V }
    have hψK' : ∀ k : K, ψ' (algebraMap K _ k) = (χ'.comp io₀) k := by
      intro k
      obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := T₀.V) (io₀ k)
      have hb0 : algebraMap T₀.V T₀.Fr b ≠ 0 := by simpa using nonZeroDivisors.ne_zero hb
      have h1 : io₀ k * algebraMap T₀.V _ b = algebraMap T₀.V _ a := by
        rw [← hab, div_mul_cancel₀ _ hb0]
      have h2 := hψ' (algebraMap K _ k) _ _ (hK j k a b h1)
      rw [hρ, hρ, ← hχ', ← hχ', ← h1, map_mul] at h2
      exact mul_right_cancel₀ ((map_ne_zero χ').2 hb0) h2
    obtain ⟨v, hv'⟩ : ψ' r ∈ Set.range (algebraMap V (FractionRing V)) :=
      hr T' (χ'.comp io₀) (m * 1) (hov.bc χ' hm hv) (hfin' hfin) ψ' hψK' (fun y hy => by
        obtain ⟨x, hx⟩ := hg j y hy
        have := hψ' y x 1 (by rw [map_one, _root_.mul_one, hx])
        rw [map_one, map_one, _root_.mul_one] at this
        exact ⟨ρ x, this.symm⟩)
    refine ⟨v, IsFractionRing.injective V (FractionRing V) ?_⟩
    rw [← hψ' r a b hab, ← hv', map_mul, _root_.mul_comm])
  have hm : φ' (s - 1) ∈ IsLocalRing.maximalIdeal T.V := by
    refine (Ideal.map_le_iff_le_comap (K := (IsLocalRing.maximalIdeal T.V).comap φ')).2 ?_ hs
    intro a ha
    change φ' (algebraMap T₀.V (A j) a) ∈ IsLocalRing.maximalIdeal T.V
    rw [hc]
    exact fun hu => ha (hloc.map_nonunit a hu)
  have hu : IsUnit (φ' s) := by
    by_contra hnu
    have h1 : φ' s - φ' (s - 1) ∈ IsLocalRing.maximalIdeal T.V := sub_mem hnu hm
    rw [← map_sub, sub_sub_cancel, map_one] at h1
    exact h1 isUnit_one
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have h2 := hφψ r x s hxs
  refine ⟨φ' x * w, ?_⟩
  rw [map_mul, hφ', ← h2, ← hφ', _root_.mul_assoc, ← map_mul, hw, map_one, _root_.mul_one]

end GlobalTheory.ChartIntegral
end

section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.acrisValuation_radius_laws : ∀ (l : ℕ) [Fact l.Prime] (r : ℝ), 0 < r → r ≤ 1 → (∀ x y : Formalism.Per.Acris l, x ≠ 0 → y ≠ 0 → vr l r (x * y) = vr l r x + vr l r y) ∧ (∀ x : Formalism.Per.Acris l, x ≠ 0 → φc l x ≠ 0 ∧ vr l r (φc l x) = l * vr l (r / l) x) ∧ (∀ (x : Formalism.Per.Acris l) (n : ℕ), x ≠ 0 → vr l r ((l : Formalism.Per.Acris l) ^ n * x) = n * r + vr l r x) ∧ ∀ x : Formalism.Per.Acris l, x ≠ 0 → vr l r x = -Real.logb l (gC l ((l : ℝ) ^ (-r)) x) := by
  first | exact @GlobalTheory.PMon.Gauss.vr_laws | exact GlobalTheory.PMon.Gauss.vr_laws | (intros; apply GlobalTheory.PMon.Gauss.vr_laws <;> assumption)
end

section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.gaussNormAcris_locally_monomial : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), x ≠ 0 → ∀ ρ₀ : ℝ, (l : ℝ)⁻¹ ≤ ρ₀ → ρ₀ < 1 → (∃ (c : ℝ) (k : ℤ) (ρ₂ : ℝ), 0 < c ∧ ρ₀ < ρ₂ ∧ ρ₂ < 1 ∧ ∀ ρ ∈ Set.Icc ρ₀ ρ₂, gC l ρ x = c * ρ ^ k) ∧ ((l : ℝ)⁻¹ < ρ₀ → ∃ (c : ℝ) (k : ℤ) (ρ₁ : ℝ), 0 < c ∧ (l : ℝ)⁻¹ ≤ ρ₁ ∧ ρ₁ < ρ₀ ∧ ∀ ρ ∈ Set.Icc ρ₁ ρ₀, gC l ρ x = c * ρ ^ k) := by
  first | exact @GlobalTheory.PMon.Gauss.gC_monomial_near | exact GlobalTheory.PMon.Gauss.gC_monomial_near | (intros; apply GlobalTheory.PMon.Gauss.gC_monomial_near <;> assumption)
end
