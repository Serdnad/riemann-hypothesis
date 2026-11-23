module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle104
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle032
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle053
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFramesDifferByUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1180
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
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaUnfold

open GlobalTheory.WeilM
open scoped Classical

theorem continuous_infToMixed (F : Type) [Field F] [NumberField F] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F =>
    ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
     (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem adele_nontrivial (F : Type) [Field F] [NumberField F] : Nontrivial (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (Nontrivial (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem schA_continuous (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schA F κ) : Continuous Φ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    refine (f.continuous.comp ?_).mul (hg.1.continuous.comp ?_)
    · exact continuous_pi fun i =>
        (continuous_infToMixed F).comp (continuous_fst.comp (continuous_apply i))
    · exact continuous_pi fun i => continuous_snd.comp (continuous_apply i)
  | zero => exact continuous_const
  | add Φ Ψ _ _ h1 h2 => exact h1.add h2
  | smul c Φ _ h => exact continuous_const.mul h

def ratEquiv (F : Type) [Field F] [NumberField F] (κ : Type) : (κ → F) ≃ GlobalTheory.ThetaParseval.ratVec F κ :=
  Equiv.ofBijective
    (fun ξ => ⟨fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i), (GlobalTheory.ThetaParseval.mem_ratVec_iff _).2 ⟨ξ, rfl⟩⟩)
    ⟨fun a b h => funext fun i => (haveI := adele_nontrivial F; (algebraMap F (AdeleRing (𝓞 F) F)).injective) (congrFun (congrArg Subtype.val h) i),
     fun y => by
      obtain ⟨ξ, hξ⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff y.1).1 y.2
      exact ⟨ξ, Subtype.ext hξ.symm⟩⟩

theorem unfold : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (𝓕₁ : Set (κ → AF F)), @IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) _ _ _ (borel _) 𝓕₁ μ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
      ∫⁻ x in 𝓕₁, ∑' ξ : κ → F, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + x)‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ _ μ hμ 𝓕₁ h𝓕 Φ hΦ
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  have hc := schA_continuous F hΦ
  haveI : Countable F := by
    have b := Module.finBasis ℚ F
    exact Countable.of_equiv _ b.equivFun.toEquiv.symm
  haveI : Countable (GlobalTheory.ThetaParseval.ratVec F κ) := Countable.of_equiv _ (ratEquiv F κ)
  have hm : ∀ c : κ → AF F, Measurable fun x : κ → AF F => ‖Φ (c + x)‖ₑ ^ 2 := fun c =>
    ((hc.comp (continuous_const.add continuous_id)).measurable.enorm).pow_const 2
  rw [lintegral_tsum fun ξ => (hm _).aemeasurable, h𝓕.lintegral_eq_tsum' (fun x => ‖Φ x‖ₑ ^ 2)]
  rw [← ((ratEquiv F κ).trans (Equiv.neg _)).tsum_eq]
  refine tsum_congr fun ξ => ?_
  simp only [Equiv.trans_apply, Equiv.neg_apply, neg_neg, AddSubgroup.vadd_def, vadd_eq_add]
  rfl
end GlobalTheory.ThetaUnfold
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped Pointwise

namespace GlobalTheory.PeriodicIterated

section General

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]

theorem prod_isAddFundamentalDomain (Γ₁ : AddSubgroup V) (Γ : AddSubgroup (V × V))
    (hΓ : ∀ w : V × V, w ∈ Γ ↔ w.1 ∈ Γ₁ ∧ w.2 ∈ Γ₁) (μ : Measure V) [SFinite μ]
    (𝓕₁ : Set V) (h : IsAddFundamentalDomain Γ₁ 𝓕₁ μ) :
    IsAddFundamentalDomain Γ (𝓕₁ ×ˢ 𝓕₁) (μ.prod μ) := by
  refine ⟨h.nullMeasurableSet.prod h.nullMeasurableSet, ?_, ?_⟩
  · have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae h.ae_covers
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae h.ae_covers
    filter_upwards [h1, h2] with p ha hb
    obtain ⟨a, ha⟩ := ha
    obtain ⟨b, hb⟩ := hb
    exact ⟨⟨((a : V), (b : V)), (hΓ _).2 ⟨a.2, b.2⟩⟩, ha, hb⟩
  · intro g g' hne
    have hset : ∀ k : Γ, k +ᵥ (𝓕₁ ×ˢ 𝓕₁) =
        ((⟨(k : V × V).1, ((hΓ _).1 k.2).1⟩ : Γ₁) +ᵥ 𝓕₁) ×ˢ
          ((⟨(k : V × V).2, ((hΓ _).1 k.2).2⟩ : Γ₁) +ᵥ 𝓕₁) := by
      intro k
      ext ⟨x, y⟩
      simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_prod, AddSubgroup.vadd_def,
        AddSubgroup.coe_neg, vadd_eq_add, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]
    show μ.prod μ ((g +ᵥ (𝓕₁ ×ˢ 𝓕₁)) ∩ (g' +ᵥ (𝓕₁ ×ˢ 𝓕₁))) = 0
    rw [hset g, hset g', Set.prod_inter_prod, Measure.prod_prod]
    by_cases h1 : (g : V × V).1 = (g' : V × V).1
    · have h2 : (g : V × V).2 ≠ (g' : V × V).2 := by
        intro h2
        exact hne (Subtype.ext (Prod.ext h1 h2))
      have := h.aedisjoint (i := ⟨(g : V × V).2, ((hΓ _).1 g.2).2⟩)
        (j := ⟨(g' : V × V).2, ((hΓ _).1 g'.2).2⟩) (fun h' => h2 (congrArg Subtype.val h'))
      rw [show μ _ = 0 from this, mul_zero]
    · have := h.aedisjoint (i := ⟨(g : V × V).1, ((hΓ _).1 g.2).1⟩)
        (j := ⟨(g' : V × V).1, ((hΓ _).1 g'.2).1⟩) (fun h' => h1 (congrArg Subtype.val h'))
      rw [show μ _ = 0 from this, zero_mul]

theorem lintegral_fundamentalDomain_eq_iterated (Γ₁ : AddSubgroup V) [Countable Γ₁]
    (Γ : AddSubgroup (V × V)) (hΓ : ∀ w : V × V, w ∈ Γ ↔ w.1 ∈ Γ₁ ∧ w.2 ∈ Γ₁)
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (mW : MeasurableSpace (V × V)) (hmW : mW = Prod.instMeasurableSpace)
    (ν : @Measure (V × V) mW) (hν : @Measure.IsAddHaarMeasure _ _ _ mW ν)
    (𝓕 : Set (V × V)) (h𝓕 : @IsAddFundamentalDomain Γ _ _ _ mW 𝓕 ν)
    (𝓕₁ : Set V) (h𝓕₁ : IsAddFundamentalDomain Γ₁ 𝓕₁ μ) :
    ∃ c₁ : ENNReal, c₁ ≠ 0 ∧ c₁ ≠ ⊤ ∧ ∀ G : V × V → ENNReal, @Measurable _ _ mW _ G →
      (∀ γ ∈ Γ, ∀ w, G (γ + w) = G w) →
      ∫⁻ w in 𝓕, G w ∂ν = c₁ * ∫⁻ x in 𝓕₁, ∫⁻ y in 𝓕₁, G (x, y) ∂μ ∂μ := by
  subst hmW
  haveI := hν
  haveI : Countable Γ := by
    have hinj : Function.Injective (fun k : Γ =>
        ((⟨(k : V × V).1, ((hΓ _).1 k.2).1⟩ : Γ₁), (⟨(k : V × V).2, ((hΓ _).1 k.2).2⟩ : Γ₁))) := by
      intro k k' hk
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at hk
      exact Subtype.ext (Prod.ext hk.1 hk.2)
    exact hinj.countable
  have hmeq := Measure.isAddLeftInvariant_eq_smul ν (μ.prod μ)
  set c : NNReal := Measure.addHaarScalarFactor ν (μ.prod μ)
  have hcpos : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν (μ.prod μ)
  have hν' : ν = (c : ENNReal) • μ.prod μ := by
    rw [← ENNReal.smul_def]; exact hmeq
  refine ⟨(c : ENNReal), by exact_mod_cast hcpos.ne', ENNReal.coe_ne_top, fun G hG hper => ?_⟩
  have hD : IsAddFundamentalDomain Γ (𝓕₁ ×ˢ 𝓕₁) ν :=
    (prod_isAddFundamentalDomain Γ₁ Γ hΓ μ 𝓕₁ h𝓕₁).mono (by rw [hν']; exact Measure.smul_absolutelyContinuous)
  rw [h𝓕.setLIntegral_eq hD G (fun g x => hper g g.2 x), hν', Measure.restrict_smul,
    lintegral_smul_measure, ← Measure.prod_restrict, lintegral_prod _ hG.aemeasurable, smul_eq_mul]

end General

end GlobalTheory.PeriodicIterated

namespace GlobalTheory.PeriodicIterated

theorem countable_ratVec (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    Countable (GlobalTheory.ThetaParseval.ratVec F κ) := by
  haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  exact (AddMonoidHom.rangeRestrict_surjective _).countable

theorem mem_ratPair_iff_ratVec (F : Type) [Field F] [NumberField F] (κ : Type)
    (w : (κ → AF F) × (κ → AF F)) :
    w ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ ↔
      w.1 ∈ GlobalTheory.ThetaParseval.ratVec F κ ∧ w.2 ∈ GlobalTheory.ThetaParseval.ratVec F κ := by
  rw [GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff, GlobalTheory.ThetaParseval.mem_ratVec_iff,
    GlobalTheory.ThetaParseval.mem_ratVec_iff]
  constructor
  · rintro ⟨y, z, rfl⟩
    exact ⟨⟨y, rfl⟩, ⟨z, rfl⟩⟩
  · rintro ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    exact ⟨y, z, Prod.ext hy hz⟩

theorem lintegral_ratPair_fundamentalDomain_eq_iterated : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (ν : @Measure ((κ → AF F) × (κ → AF F)) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ (𝓕 : Set ((κ → AF F) × (κ → AF F))), @IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F κ) _ _ _ (borel _) 𝓕 ν →
    ∀ (𝓕₁ : Set (κ → AF F)), @IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) _ _ _ (borel _) 𝓕₁ μ →
    ∃ c₁ : ENNReal, c₁ ≠ 0 ∧ c₁ ≠ ⊤ ∧ ∀ G : (κ → AF F) × (κ → AF F) → ENNReal, @Measurable _ _ (borel _) _ G →
      (∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, ∀ w, G (γ + w) = G w) →
      ∫⁻ w in 𝓕, G w ∂ν = c₁ * ∫⁻ x in 𝓕₁, ∫⁻ y in 𝓕₁, G (x, y) ∂μ ∂μ := by
  intro F _ _ κ _ μ hμ ν hν 𝓕 h𝓕 𝓕₁ h𝓕₁
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := countable_ratVec F κ
  haveI := hμ
  exact lintegral_fundamentalDomain_eq_iterated (GlobalTheory.ThetaParseval.ratVec F κ)
    (GlobalTheory.WeilUnitaryTransport.ratPair F κ) (mem_ratPair_iff_ratVec F κ) μ (borel _)
    (Prod.borelSpace (α := κ → AF F) (β := κ → AF F)).measurable_eq.symm ν hν 𝓕 h𝓕 𝓕₁ h𝓕₁

end GlobalTheory.PeriodicIterated

end
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
open ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace GlobalTheory.PtDeg.FrameEig

theorem dualMapR_epsScaleR {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (a : R) :
    spMap (Chart.dualMapR f) ≫ spMap (epsScaleR a) = spMap (epsMul (f a)) ≫ spMap (Chart.dualMapR f) := by
  rw [GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂]
  congr 1
  apply RingHom.ext
  intro r
  ext <;> simp [epsMul, epsScaleR, Chart.dualMapR, mul_comm]

theorem epsScaleR_epsMul_comm {R : Type} [CommRing R] (a b : R) :
    spMap (epsScaleR a) ≫ spMap (epsMul b) = spMap (epsMul b) ≫ spMap (epsScaleR a) := by
  rw [GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂]
  congr 1
  apply RingHom.ext
  intro r
  ext <;> simp [epsMul, epsScaleR, mul_left_comm]

theorem scale_eig {R : Type} [CommRing R] {X : Scheme.{0}} (a b : R) (x : Sp (DualNumber R) ⟶ X) (g : X ⟶ X)
    (h : x ≫ g = spMap (epsMul b) ≫ x) :
    (spMap (epsScaleR a) ≫ x) ≫ g = spMap (epsMul b) ≫ spMap (epsScaleR a) ≫ x := by
  rw [Category.assoc, h, ← Category.assoc, epsScaleR_epsMul_comm, Category.assoc]

theorem epsScaleR_eq_epsMul {R : Type} [CommRing R] (a : R) : epsScaleR a = epsMul a := rfl

theorem sc_left {R : Type} [CommRing R] {G : Over (Sp R)} (a : R) (v : epsR R ⟶ G) :
    (GlobalTheory.CM.IntCoord.sc a ≫ v).left = spMap (epsScaleR a) ≫ v.left := rfl

end GlobalTheory.PtDeg.FrameEig


open GlobalTheory.PtDeg.FrameEig in
theorem GlobalTheory.PtDeg.frameCoord_mem_span_eigLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (tt : 𝓞 E →+* 𝓞 K), (∀ a, ((tt a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ a)) → ∀ (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ j, u j ∈ Submodule.span K (F.eigLat B.t.act tt : Set (Fin F.P₀.g → K)) := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 F ρ tt htt u hu j
  obtain ⟨u₀, w, h₁, h₂, hc⟩ := hu j
  have h₂' : u₀ ≫ m2.cm.F = w.left ≫ F.φ := h₂
  have h₁' : u₀ ≫ m1.cm.F = y.u ρ j := h₁

  have hbase : u₀ ≫ t₀.G.hom = spMap (algebraMap K (DualNumber K)) := by
    apply GlobalTheory.IntLie.spMap_frac_cancel (V := 𝓞 K)
    rw [Category.assoc, ← m2.cart.1.w, ← Category.assoc, h₂', Category.assoc]
    have e := F.fib.2.1.1.w
    erw [e]
    rw [← Category.assoc, Over.w w]
    rfl

  have hact0 : ∀ a : 𝓞 E, u₀ ≫ (t₀.act.act a).left = spMap (epsMul ((tt a : 𝓞 K) : K)) ≫ u₀ := by
    intro a
    apply m1.cart.1.hom_ext
    · rw [Category.assoc, m1.act a, ← Category.assoc, h₁', y.eig ρ j a, htt a, Category.assoc, h₁']
    · rw [Category.assoc, Over.w (t₀.act.act a), hbase, Category.assoc, hbase, GlobalTheory.IntLie.spMap_comp₂,
        GlobalTheory.IntLie.epsMul_alg]

  have hw : ∀ a : 𝓞 E, w.left ≫ F.φ ≫ (B.t.act.act a).left =
      spMap (epsMul ((tt a : 𝓞 K) : K)) ≫ w.left ≫ F.φ := by
    intro a
    rw [← reassoc_of% h₂', ← m2.act a, ← Category.assoc, hact0, Category.assoc, h₂']

  have hc' : u j ∈ Submodule.span K (F.lieLat : Set (Fin F.P₀.g → K)) := by
    rw [(GlobalTheory.CM.LieLattice.lieLat_fg_and_span_eq_top K B.pol F).2]; trivial
  obtain ⟨d, hd⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ (u j) hc'
  rw [Submodule.span_eq, Submonoid.smul_def] at hd
  obtain ⟨-, -, -, -, hlat, heig⟩ := GlobalTheory.CM.integral_tangent_coordinates K B.pol F
  obtain ⟨U, hUt, w₁, hUv, hw₁⟩ := (hlat _).1 hd
  have := F.P₀.isAb.comm
  have hK := GlobalTheory.LieComb.lieComb_algebra K F.P₀.A _ F.v F.basis.1
  set dK : K := algebraMap (𝓞 K) K (d : 𝓞 K) with hdK
  have hw₁' : w₁ = GlobalTheory.CM.IntCoord.sc dK ≫ w := by
    have h3 := hK.2.2.1 1 ![u j] ![w] ![dK] _ (fun i => by fin_cases i; exact hc)
      ((GlobalTheory.CM.IntCoord.isLieComb_one_iff _ _ _).2 rfl)
    simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Matrix.cons_val_fin_one,
      Finset.sum_singleton] at h3
    rw [← algebraMap_smul K (d : 𝓞 K) (u j)] at hw₁
    exact (hK.1 _).unique hw₁ h3
  have hw₁e : ∀ a : 𝓞 E, w₁.left ≫ F.φ ≫ (B.t.act.act a).left =
      spMap (epsMul ((tt a : 𝓞 K) : K)) ≫ w₁.left ≫ F.φ := by
    intro a
    rw [hw₁', sc_left, Category.assoc, Category.assoc]
    have := scale_eig dK ((tt a : 𝓞 K) : K) (w.left ≫ F.φ) (B.t.act.act a).left (by rw [Category.assoc, hw a])
    simpa only [Category.assoc] using this

  have := B.pol.isAb.proper
  have hmem : (d : 𝓞 K) • u j ∈ F.eigLat B.t.act tt := by
    rw [heig]
    refine ⟨U, ⟨hUt, w₁, hUv, hw₁⟩, fun a => ?_⟩
    rw [GlobalTheory.CM.IntCoord.isLieComb_one_iff]
    have hv1 : IsVecOver (algebraMap (𝓞 K) K) F.φ (U ≫ B.t.act.act a)
        (GlobalTheory.CM.IntCoord.sc ((tt a : 𝓞 K) : K) ≫ w₁) := by
      unfold IsVecOver at hUv ⊢
      rw [sc_left, Over.comp_left, ← Category.assoc, ← hUv, Category.assoc, Category.assoc, hw₁e a,
        epsScaleR_eq_epsMul]
    have hv2 : IsVecOver (algebraMap (𝓞 K) K) F.φ (GlobalTheory.CM.IntCoord.sc (tt a) ≫ U)
        (GlobalTheory.CM.IntCoord.sc ((tt a : 𝓞 K) : K) ≫ w₁) := by
      unfold IsVecOver at hUv ⊢
      rw [sc_left, sc_left, Category.assoc, hUv, epsScaleR_eq_epsMul]
      have e := dualMapR_epsScaleR (algebraMap (𝓞 K) K) (tt a)
      exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ U.left) e).trans (Category.assoc _ _ _))).symm
    exact GlobalTheory.CM.IntCoord.eq_of_isVecOver (IsFractionRing.injective (𝓞 K) K) hv1 hv2

  have hd0 : dK ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 (nonZeroDivisors.coe_ne_zero d)
  have h₃ := Submodule.smul_mem (Submodule.span K (F.eigLat B.t.act tt : Set (Fin F.P₀.g → K))) dK⁻¹
    (Submodule.subset_span hmem)
  rwa [← algebraMap_smul K (d : 𝓞 K) (u j), ← hdK, inv_smul_smul₀ hd0] at h₃
end
end

section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

noncomputable section

namespace GlobalTheory

namespace WeylCellRankOne

variable {L : Type} [Field L] {n : ℕ}

theorem conj_apply {s : Equiv.Perm (Fin n)} {y : GL (Fin n) L} (hy : IsWeylRep s y)
    (M : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    ((y⁻¹ : GL (Fin n) L) * M * (y : Matrix (Fin n) (Fin n) L)) i j =
      ((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (s i) * M (s i) (s j) *
        (y : Matrix (Fin n) (Fin n) L) (s j) j := by
  have hi := hy.inv
  rw [Matrix.mul_apply, Finset.sum_eq_single (s j)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (s i)]
    · intro b _ hb
      rw [hi i b (by intro h; apply hb; rw [h]; simp), zero_mul]
    · simp
  · intro b _ hb; rw [hy b j hb, mul_zero]
  · simp

theorem diag_mul_eq_one {s : Equiv.Perm (Fin n)} {y : GL (Fin n) L} (hy : IsWeylRep s y) (i : Fin n) :
    ((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (s i) *
        (y : Matrix (Fin n) (Fin n) L) (s i) i = 1 := by
  have h := conj_apply hy 1 i i
  rw [Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply_eq,
    Matrix.one_apply_eq, mul_one] at h
  exact h.symm

theorem swap_lt {a b p q : Fin n} (hab : b.val = a.val + 1) (hpq : p < q) (hne : ¬ (p = a ∧ q = b)) :
    Equiv.swap a b p < Equiv.swap a b q := by
  rw [Fin.lt_def] at hpq ⊢
  have ha : ∀ x : Fin n, x = a ↔ x.val = a.val := fun x => Fin.ext_iff
  have hb : ∀ x : Fin n, x = b ↔ x.val = b.val := fun x => Fin.ext_iff
  simp only [Equiv.swap_apply_def]
  rw [ha, hb] at hne
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;> simp only [ha, hb] at * <;> omega

theorem mem_cell_swap {a b : Fin n} (hab : b.val = a.val + 1) {y : GL (Fin n) L}
    (hy : IsWeylRep (Equiv.swap a b) y) (u : GL (Fin n) L) :
    u ∈ cell y ↔ ∀ i j, ¬ (i = a ∧ j = b) →
      (u : Matrix (Fin n) (Fin n) L) i j = (1 : Matrix (Fin n) (Fin n) L) i j := by
  set s := Equiv.swap a b with hs
  have hd := diag_mul_eq_one hy
  have hne1 : ∀ i, ((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (s i) ≠ 0 :=
    fun i h => by have := hd i; rw [h, zero_mul] at this; exact zero_ne_one this
  have hne2 : ∀ i, (y : Matrix (Fin n) (Fin n) L) (s i) i ≠ 0 :=
    fun i h => by have := hd i; rw [h, mul_zero] at this; exact zero_ne_one this
  have hconj : ∀ i j, ((y⁻¹ * u * y : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      ((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (s i) * (u : Matrix (Fin n) (Fin n) L) (s i) (s j) *
        (y : Matrix (Fin n) (Fin n) L) (s j) j := by
    intro i j; rw [Units.val_mul, Units.val_mul]; exact conj_apply hy _ i j
  have hss : ∀ x, s (s x) = x := fun x => Equiv.swap_apply_self a b x
  have hlt : a < b := by rw [Fin.lt_def]; omega
  rw [mem_cell, mem_unipB, mem_unipBLower]
  constructor
  · rintro ⟨⟨hup, hdiag⟩, hlow, -⟩ i j hij
    rcases lt_trichotomy i j with h | rfl | h
    · rw [Matrix.one_apply_ne h.ne]
      have h2 := hlow (s i) (s j) (swap_lt hab h hij)
      rw [hconj] at h2
      rcases mul_eq_zero.1 h2 with h3 | h3
      · rcases mul_eq_zero.1 h3 with h4 | h4
        · exact absurd h4 (hne1 _)
        · rwa [hss, hss] at h4
      · exact absurd h3 (hne2 _)
    · rw [Matrix.one_apply_eq]; exact hdiag i
    · rw [Matrix.one_apply_ne h.ne']; exact hup i j h
  · intro h
    have hdiag : ∀ i, (u : Matrix (Fin n) (Fin n) L) i i = 1 := fun i => by
      rw [h i i (fun hh => by rw [← hh.1, ← hh.2] at hlt; exact lt_irrefl _ hlt), Matrix.one_apply_eq]
    refine ⟨⟨fun i j hji => ?_, hdiag⟩, fun i j hij => ?_, fun i => ?_⟩
    · rw [h i j (fun hh => by rw [hh.1, hh.2] at hji; exact lt_asymm hji hlt), Matrix.one_apply_ne hji.ne']
    · rw [hconj, h (s i) (s j), Matrix.one_apply_ne, mul_zero, zero_mul]
      · intro he; exact hij.ne (s.injective he)
      · rintro ⟨h1, h2⟩
        have e1 : i = b := by rw [← hss i, h1]; exact Equiv.swap_apply_left a b
        have e2 : j = a := by rw [← hss j, h2]; exact Equiv.swap_apply_right a b
        rw [e1, e2] at hij; exact lt_asymm hij hlt
    · rw [hconj, hdiag, mul_one]; exact hd i

end WeylCellRankOne

open WeylCellRankOne in
theorem cellU_rankOne_shape : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ)
    (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → Even n → ∀ (y : GU σ n),
    IsWeylRep (simpleU k) (y : GL (Fin n) L) → ∀ (u : GU σ n),
    u ∈ cellU y ↔ ∀ i j, ¬ (i = lo k ∧ j = (lo k).rev) →
      ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = (1 : Matrix (Fin n) (Fin n) L) i j := by
  intro L _ _ σ n k hk he y hy u
  have hs : simpleU k = Equiv.swap (lo k) (lo k).rev := by simp [simpleU, hk]
  rw [hs] at hy
  have hab : ((lo k).rev).val = (lo k).val + 1 := by
    obtain ⟨m, rfl⟩ := he
    have hk2 := k.isLt
    simp only [Fin.val_rev, lo, Fin.coe_castLE]
    omega
  rw [cellU, Subgroup.mem_subgroupOf]
  exact mem_cell_swap hab hy (u : GL (Fin n) L)

end GlobalTheory
end
end
