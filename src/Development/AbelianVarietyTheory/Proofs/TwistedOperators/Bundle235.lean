module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanPairNegativeSymplecticPairing
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle081
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducible
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle274
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle256
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeFunctionConstantTermVanishSplitPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle148
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMatrixOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle171
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle227
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle229
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.HermitianPerpSubgroup
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open scoped Classical

theorem _root_.GlobalTheory.T.exists_archimedean_pair_negative_symplectic_pairing : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (B : Base F E) {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → 0 < n → 0 < d →
    ∀ (ε' : InfinitePlace F → ℤˣ) (w : InfinitePlace F), ε' w = -1 →
    ∃ u u' : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u ∧ At (evI F) u' ∧
      (∀ w', u'.map (piInf (B.emb w')) =
        (((ε' w' : ℤ) : ℂ) * Complex.I) • (X.θ w' * u.map (piInf (B.emb w')) * (W.θ w')ᵀ)) ∧
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (evI F (GlobalTheory.WeilM.symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) u u')) < 0 := by
  first | exact @GlobalTheory.WrongSignPair.exists_neg_pair | exact GlobalTheory.WrongSignPair.exists_neg_pair | (intros; apply GlobalTheory.WrongSignPair.exists_neg_pair <;> assumption)
end

section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.thetaModels_eq_coverDiscreteSeries : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D := by
  first | exact @GlobalTheory.modelsAreCoverSeries_of_hypotheses | exact GlobalTheory.modelsAreCoverSeries_of_hypotheses | (intros; apply GlobalTheory.modelsAreCoverSeries_of_hypotheses <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains GlobalTheory.PRep GlobalTheory.LFun
open Formalism.UG (IsCommensurated Hecke)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

namespace GlobalTheory.SplitChoice

theorem exists_place_over (K : Type) [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal := by
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) (Ideal.span {(p : ℤ)})
    (by rw [(RingHom.injective_iff_ker_eq_bot (algebraMap ℤ (𝓞 K))).1 (FaithfulSMul.algebraMap_injective _ _)]; exact bot_le)
  have hm : ((p : ℕ) : 𝓞 K) ∈ Q := by
    have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := by
      change (p : ℤ) ∈ Ideal.under ℤ Q
      rw [hQc]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ.isPrime, fun h0 => ?_⟩, hm⟩
  rw [h0, Ideal.mem_bot] at hm
  exact hp.ne_zero (by exact_mod_cast hm)

theorem natCast_notMem_of_absNorm_lt {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {p : ℕ}
    (hp : p.Prime) (h : Ideal.absNorm v.asIdeal < p) : (p : 𝓞 K) ∉ v.asIdeal := by
  intro hmem
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hcop : Nat.Coprime p (Ideal.absNorm v.asIdeal) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd) (by omega)
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (𝓞 K))
  simp only [eq_intCast, Int.cast_natCast] at hab
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ (Ideal.absNorm_mem _))))

theorem splitsCompletely_of_modEq_one (D : D7) {p : ℕ} (hp : p.Prime)
    (hc : p ≡ 1 [MOD D.host.QS * D.host.q * D.host.d]) : SplitsCompletely D p := by
  obtain ⟨h1, -, h3⟩ := GlobalTheory.HostSplit.split_completely_of_modEq_one D.R D.host p hp hc
  have hs : GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentStabilizers.SplitsCompletely D.host.E p := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentStabilizers.SplitsCompletely
    rw [GlobalTheory.SplitResidue.card_eq_ncard_primesOver D.host.E hp, ← GlobalTheory.HostSplit.ncard_placesOver D.host.E hp, h1]
  refine ⟨hp, fun w hw => ⟨h3 w hw, ?_⟩⟩
  haveI := w.isPrime
  have hs' := (GlobalTheory.SplitResidue.card_eq_ncard_primesOver D.host.E hp).symm.trans hs
  exact (GlobalTheory.LocSplit.split_prime hp hs' w.asIdeal hw).1

theorem exists_split_prime : ∀ (D : D7) (S : Set (HeightOneSpectrum (𝓞 D.host.F))) (N : ℕ), S.Finite → N ≠ 0 →
    ∃ p : ℕ, SplitsCompletely D p ∧ p.Coprime N ∧ (∀ v ∈ S, (p : 𝓞 D.host.F) ∉ v.asIdeal) ∧
      ∃ v : HeightOneSpectrum (𝓞 D.host.F), (p : 𝓞 D.host.F) ∈ v.asIdeal := by
  intro D S N hS hN
  have hn : D.host.QS ≠ 0 := D.host.QS_pos.ne'
  have hq : D.host.q ≠ 0 := D.host.hyp.1.ne_zero
  have hd : D.host.d ≠ 0 := D.host.hyp.2.1.ne_zero
  have hm : D.host.QS * D.host.q * D.host.d ≠ 0 := by positivity
  obtain ⟨p, hp, hlt, hc⟩ := Nat.exists_prime_gt_modEq_one
    (N + ∑ v ∈ hS.toFinset, Ideal.absNorm v.asIdeal) hm
  refine ⟨p, splitsCompletely_of_modEq_one D hp hc, ?_, fun v hv => ?_, exists_place_over _ hp⟩
  · refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun hdv => ?_
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hdv
    omega
  · refine natCast_notMem_of_absNorm_lt v hp ?_
    have := Finset.single_le_sum (f := fun v : HeightOneSpectrum (𝓞 D.host.F) => Ideal.absNorm v.asIdeal)
      (fun _ _ => Nat.zero_le _) (hS.mem_toFinset.2 hv)
    omega

end GlobalTheory.SplitChoice
end

section

open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal

namespace GlobalTheory.ClassTerm

theorem hasClassInt_of_lintegral_eq : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup H) [DiscreteTopology Γ] (γ : H), γ ∈ Γ → ∀ (μ : Measure H) (𝓕 : Set H) (ν : Measure (Quot (cent γ))) (a : ℝ≥0∞), a < ⊤ → (∀ G : H → ℝ≥0∞, Measurable G → ∫⁻ x in 𝓕, ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, G (x⁻¹ * δ * x) ∂μ = a * ∫⁻ q, G (q.out⁻¹ * γ * q.out) ∂ν) → ∀ (f : H → ℂ) (c : ℂ), Continuous f → HasCompactSupport f → Integrable (fun q : Quot (cent γ) => f (q.out⁻¹ * γ * q.out)) ν → ∫ q, f (q.out⁻¹ * γ * q.out) ∂ν = c → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.HasClassInt Γ μ 𝓕 γ f (a.toReal * c) := by
  intro H _ _ _ _ _ _ _ _ Γ _ γ hγ μ 𝓕 ν a ha hL f c hf hfc hint hc
  classical
  have hmemΓ : ∀ δ ∈ GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, δ ∈ Γ := by
    rintro _ ⟨g, hg, rfl⟩
    exact mul_mem (mul_mem (inv_mem hg) hγ) hg
  let ι : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ → Γ := fun δ => ⟨δ, hmemΓ _ δ.2⟩
  have hι : Function.Injective ι := fun a b h => Subtype.ext (congrArg Subtype.val h :)
  haveI : Countable (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ) := hι.countable
  have hcont : ∀ δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, Continuous fun x : H => x⁻¹ * (δ : H) * x := fun δ => by
    fun_prop
  have hfm : Measurable f := hf.measurable
  have hfs : StronglyMeasurable f := hf.stronglyMeasurable

  have hfin : ∀ x, (Function.support fun δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ => f (x⁻¹ * δ * x)).Finite := by
    intro x
    have hC : IsCompact ((fun z => x * z * x⁻¹) '' tsupport f) := hfc.isCompact.image (by fun_prop)
    refine ((finite_mem_compact (Γ := Γ) hC).preimage hι.injOn).subset ?_
    intro δ hδ
    refine ⟨x⁻¹ * δ * x, subset_tsupport f hδ, ?_⟩
    show x * (x⁻¹ * (δ : H) * x) * x⁻¹ = δ
    group
  have hsum : ∀ x, Summable fun δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ => f (x⁻¹ * δ * x) := fun x =>
    summable_of_hasFiniteSupport (hfin x)

  have hem : Measurable (fun q : Quot (cent γ) => q.out⁻¹ * γ * q.out) := by
    have hli : LeftInv (cent γ) (fun x : H => x⁻¹ * γ * x) := by
      intro t ht x
      have hcomm : γ * t = t * γ := Subgroup.mem_centralizer_iff.1 ht γ (Set.mem_singleton γ)
      have h1 : t⁻¹ * γ * t = γ := by rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
      calc (t * x)⁻¹ * γ * (t * x) = x⁻¹ * (t⁻¹ * γ * t) * x := by group
        _ = x⁻¹ * γ * x := by rw [h1]
    exact measurable_descend hli (by fun_prop : Continuous fun x : H => x⁻¹ * γ * x).measurable
  set m1 : Measure H := Measure.sum fun δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ =>
    (μ.restrict 𝓕).map (fun x => x⁻¹ * (δ : H) * x) with hm1
  set m2 : Measure H := a • ν.map (fun q : Quot (cent γ) => q.out⁻¹ * γ * q.out) with hm2
  have hm12 : m1 = m2 := Measure.ext_of_lintegral _ fun G hG => by
    rw [hm1, hm2, lintegral_sum_measure, lintegral_smul_measure, lintegral_map hG hem,
      tsum_congr (fun δ => lintegral_map hG (hcont δ).measurable), smul_eq_mul, ← hL G hG]
    exact (lintegral_tsum (f := fun (δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ) x => G (x⁻¹ * (δ : H) * x))
      (fun δ => (hG.comp (hcont δ).measurable).aemeasurable)).symm
  have hint2 : Integrable f (ν.map fun q : Quot (cent γ) => q.out⁻¹ * γ * q.out) :=
    (integrable_map_measure hfs.aestronglyMeasurable hem.aemeasurable).2 hint
  have hintm2 : Integrable f m2 := hint2.smul_measure ha.ne
  have hintm1 : Integrable f m1 := hm12 ▸ hintm2
  have hval2 : ∫ x, f x ∂m2 = (a.toReal : ℂ) * c := by
    rw [hm2, integral_smul_measure, integral_map hem.aemeasurable hfs.aestronglyMeasurable, hc, Complex.real_smul]
  have hval1 : ∫ x, f x ∂m1 = ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, ∫ x in 𝓕, f (x⁻¹ * δ * x) ∂μ := by
    rw [hm1, integral_sum_measure (hm1 ▸ hintm1)]
    exact tsum_congr fun δ => integral_map (hcont δ).measurable.aemeasurable hfs.aestronglyMeasurable
  have hfinL : ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, ∫⁻ x in 𝓕, ‖f (x⁻¹ * δ * x)‖ₑ ∂μ ≠ ∞ := by
    have h := hintm1.hasFiniteIntegral
    change ∫⁻ x, ‖f x‖ₑ ∂m1 < ∞ at h
    rw [hm1, lintegral_sum_measure] at h
    refine ne_of_lt (lt_of_eq_of_lt (tsum_congr fun δ => ?_) h)
    exact (lintegral_map hfm.enorm (hcont δ).measurable).symm
  have hKm : Measurable (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel Γ γ f) :=
    measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ)))
      (f := fun (s : Finset (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ)) x => ∑ δ ∈ s, f (x⁻¹ * (δ : H) * x))
      (fun s => Finset.measurable_sum s fun δ _ => hfm.comp (hcont δ).measurable)
      (tendsto_pi_nhds.2 fun x => (hsum x).hasSum)
  refine ⟨hsum, ⟨hKm.aestronglyMeasurable, ?_⟩, ?_⟩
  · change ∫⁻ x, ‖GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel Γ γ f x‖ₑ ∂μ.restrict 𝓕 < ∞
    calc ∫⁻ x, ‖GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel Γ γ f x‖ₑ ∂μ.restrict 𝓕
        ≤ ∫⁻ x, ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, ‖f (x⁻¹ * δ * x)‖ₑ ∂μ.restrict 𝓕 :=
          lintegral_mono fun x => enorm_tsum_le_tsum_enorm
      _ = ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, ∫⁻ x in 𝓕, ‖f (x⁻¹ * δ * x)‖ₑ ∂μ :=
          lintegral_tsum (fun δ => (hfm.comp (hcont δ).measurable).enorm.aemeasurable)
      _ < ∞ := hfinL.lt_top
  · show ∫ x in 𝓕, ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, f (x⁻¹ * δ * x) ∂μ = _
    rw [integral_tsum (f := fun (δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ) x => f (x⁻¹ * (δ : H) * x)) (fun δ => (hfm.comp (hcont δ).measurable).aestronglyMeasurable) hfinL, ← hval1, hm12, hval2]

end GlobalTheory.ClassTerm
end

section

open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal

namespace GlobalTheory.Twist.ClassSumReindex

theorem tsum_ratClass_eq_tsum_weighted (H : Type) [Group H] (Γ : Subgroup H) (γ : H) (_hγ : γ ∈ Γ)
    (α : H → ℝ≥0∞) (hα : ∀ y, ∑' h : Γ.subgroupOf (cent γ), α (((h : cent γ) : H) * y) = 1)
    (G : H → ℝ≥0∞) (x : H) :
    ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, G (x⁻¹ * δ * x) =
      ∑' g : Γ, α ((g : H) * x) * G (((g : H) * x)⁻¹ * γ * ((g : H) * x)) := by
  classical
  set C := Γ.subgroupOf (cent γ)
  let R := GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ
  let s : R → H := fun δ => Classical.choose δ.2
  have hs : ∀ δ : R, s δ ∈ Γ ∧ (δ : H) = (s δ)⁻¹ * γ * s δ := fun δ => Classical.choose_spec δ.2
  have hcomm : ∀ h : C, ((h : cent γ) : H) * γ = γ * ((h : cent γ) : H) := fun h =>
    (Subgroup.mem_centralizer_singleton_iff).1 (h : cent γ).2
  have hΓ : ∀ h : C, ((h : cent γ) : H) ∈ Γ := fun h => Subgroup.mem_subgroupOf.1 h.2
  have hconj : ∀ (h : C) (δ : R), (((h : cent γ) : H) * s δ)⁻¹ * γ * (((h : cent γ) : H) * s δ) = δ := by
    intro h δ
    rw [(hs δ).2]
    have := hcomm h
    calc (((h : cent γ) : H) * s δ)⁻¹ * γ * (((h : cent γ) : H) * s δ)
        = (s δ)⁻¹ * (((h : cent γ) : H)⁻¹ * (((h : cent γ) : H) * γ)) * s δ := by rw [this]; group
      _ = (s δ)⁻¹ * γ * s δ := by group
  let p : Γ → R := fun g => ⟨(g : H)⁻¹ * γ * g, g, g.2, rfl⟩
  have hq : ∀ g : Γ, (g : H) * (s (p g))⁻¹ ∈ cent γ := by
    intro g
    have h1 := (hs (p g)).2
    change (g : H)⁻¹ * γ * g = (s (p g))⁻¹ * γ * s (p g) at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : γ = (g : H) * ((s (p g))⁻¹ * γ * s (p g)) * (g : H)⁻¹ := by rw [← h1]; group
    calc (g : H) * (s (p g))⁻¹ * γ = (g : H) * ((s (p g))⁻¹ * γ * s (p g)) * (g : H)⁻¹ * ((g : H) * (s (p g))⁻¹) := by
          group
      _ = γ * ((g : H) * (s (p g))⁻¹) := by rw [← h2]
  let e : Γ ≃ R × C :=
    { toFun := fun g => (p g, ⟨⟨(g : H) * (s (p g))⁻¹, hq g⟩,
        Subgroup.mem_subgroupOf.2 (mul_mem g.2 (inv_mem (hs (p g)).1))⟩)
      invFun := fun q => ⟨((q.2 : cent γ) : H) * s q.1, mul_mem (hΓ q.2) (hs q.1).1⟩
      left_inv := fun g => Subtype.ext (by simp)
      right_inv := fun q => by
        obtain ⟨δ, h⟩ := q
        have hp : p ⟨((h : cent γ) : H) * s δ, mul_mem (hΓ h) (hs δ).1⟩ = δ := Subtype.ext (hconj h δ)
        refine Prod.ext hp (Subtype.ext (Subtype.ext ?_))
        simp only [hp]
        group }
  rw [← e.symm.tsum_eq]
  refine Eq.trans ?_ (ENNReal.tsum_prod (f := fun (δ : R) (h : C) => α (((e.symm (δ, h) : Γ) : H) * x) *
      G ((((e.symm (δ, h) : Γ) : H) * x)⁻¹ * γ * (((e.symm (δ, h) : Γ) : H) * x)))).symm
  refine tsum_congr fun δ => ?_
  have key : ∀ h : C, α (((e.symm (δ, h) : Γ) : H) * x) *
      G ((((e.symm (δ, h) : Γ) : H) * x)⁻¹ * γ * (((e.symm (δ, h) : Γ) : H) * x)) =
      α (((h : cent γ) : H) * (s δ * x)) * G (x⁻¹ * δ * x) := by
    intro h
    change α (((h : cent γ) : H) * s δ * x) * G ((((h : cent γ) : H) * s δ * x)⁻¹ * γ * (((h : cent γ) : H) * s δ * x)) = _
    rw [mul_assoc ((h : cent γ) : H) (s δ) x]
    congr 1
    congr 1
    rw [← hconj h δ]
    group
  rw [tsum_congr key, ENNReal.tsum_mul_right, hα, one_mul]

end GlobalTheory.Twist.ClassSumReindex
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.SplitWeil
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (radical)

theorem _root_.GlobalTheory.T.type_function_constant_term_vanish_split_place : GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.TypeConstTermVanish → ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (s : SplitAt D.sp.cm.sig V.gram (frameLat V) v) (a : ℕ), 0 < a → a < V.rank → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ (GL (Fin V.rank) (ResF v)) W), τ.IsIrreducible → GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.NoFixed τ (radical (ResF v) V.rank a) → ∀ (μ : Measure (GLoc D.sp.cm.sig V.gram v)) [μ.IsHaarMeasure], ∀ φ ∈ CcLoc D.sp.cm.sig V.gram v, ∀ f : GLoc D.sp.cm.sig V.gram v → ℂ, (f = conv μ (s.idem μ τ) φ ∨ f = conv μ φ (s.idem μ τ)) → ∀ g : GL (Fin V.rank) (Fv D.host.F v), ∃ H : Subgroup (GLoc D.sp.cm.sig V.gram v), IsClosed (H : Set (GLoc D.sp.cm.sig V.gram v)) ∧ (∀ x, x ∈ H ↔ g⁻¹ * s.equiv x * g ∈ radical (Fv D.host.F v) V.rank a) ∧ ∃ ν : Measure H, ν.IsHaarMeasure ∧ ∀ x y, ∫ u : H, f (x * u * y) ∂ν = 0 := by
  first | exact @GlobalTheory.TypeConstLoc.unipIntegral_vanish_splitAt | exact GlobalTheory.TypeConstLoc.unipIntegral_vanish_splitAt | (intros; apply GlobalTheory.TypeConstLoc.unipIntegral_vanish_splitAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heckeCharacterGrid_isAuxiliaryCharacter_testGrid : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Grid.gap D = GlobalTheory.ChiGrid.gap D 1 → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (Z : GlobalTheory.Grid.PlaceDat D), Z.S0 R.Pg = G'.pl.S0 → (∀ w, w ∈ R.Pg ∨ w ∈ Z.Wd → w.under (𝓞 D.host.F) ∈ GlobalTheory.ChiGrid.S1 D) → (∀ w ∈ Z.Wd, Formalism.L2.Host.OverP D.host D.host.pde w ∨ Formalism.L2.Host.OverP D.host D.host.pde' w) → Z.w0 = G'.pl.w G'.pl.v0 → ∀ i, 1 ≤ i → i ≤ D.R.m → Z.IsGridPlaceAuxiliaryHeckeCharacter R.Pg (fun τ => GlobalTheory.Grid.cen D τ i) (G'.ch.chiH i) := by
  first | exact @GlobalTheory.Grid.heckeCharacterGrid_isAuxiliaryCharacter_testGrid_alt | exact GlobalTheory.Grid.heckeCharacterGrid_isAuxiliaryCharacter_testGrid_alt | (intros; apply GlobalTheory.Grid.heckeCharacterGrid_isAuxiliaryCharacter_testGrid_alt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_extensionData_antiDiagonalSignGram_of_lat_eq : ∀ {D : D7} (A B : GlobalTheory.Grid.Node D) {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A.V B.V c ε) (𝔟 : Fin c → GlobalTheory.Grid.FrId D), (ε = 1 ∨ ε = -1) → B.Λ = d.lat A.Λ 𝔟 → ∃ d' : GlobalTheory.Grid.HermitianOrthogonalExtensionData A B c, d'.ι = d.ι ∧ d'.Is (fun p q => GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix c ε p q) 𝔟 := by
  first | exact @GlobalTheory.GridJoin.exists_orthogonalSum_testGrid_of_levelChoiceGrid | exact GlobalTheory.GridJoin.exists_orthogonalSum_testGrid_of_levelChoiceGrid | (intros; apply GlobalTheory.GridJoin.exists_orthogonalSum_testGrid_of_levelChoiceGrid <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.gridMinimalGap_eq_chiGridGapGamma_one : ∀ D : D7, GlobalTheory.Grid.gap D = GlobalTheory.ChiGrid.gap D 1 := by
  first | exact @GlobalTheory.GridJoin.gap_eq_chiGap | exact GlobalTheory.GridJoin.gap_eq_chiGap | (intros; apply GlobalTheory.GridJoin.gap_eq_chiGap <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.HeckeLocLift
open IsDedekindDomain Formalism.L2.NTheta
open scoped Matrix

theorem span_smul_top {D : D7} {n : ℕ} (P : Formalism.L2.DIV.Pl D.host.E) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hL : Submodule.span D.host.E (L : Set (Fin n → D.host.E)) = ⊤) :
    Submodule.span D.host.E ((P.asIdeal • L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = ⊤ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  have hx0' : ((x : D.host.E)) ≠ 0 := fun h => hx0 (RingOfIntegers.ext h)
  rw [eq_top_iff, ← hL, Submodule.span_le]
  intro w hw
  have hm : x • w ∈ (P.asIdeal • L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) := Submodule.smul_mem_smul hx hw
  have : w = (x : D.host.E)⁻¹ • (x • w) := by
    rw [← algebraMap_smul D.host.E x w]
    rw [smul_smul, inv_mul_cancel₀ (by simpa using hx0'), one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

theorem exists_hecke_ePart : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (k : ℕ) (g : GA D V)
    (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    P.asIdeal • latG V g ≤ M → M ≤ latG V g →
    M.toAddSubgroup.relIndex (latG V g).toAddSubgroup = Ideal.absNorm P.asIdeal ^ k →
    ∃ a₀ : GA D V, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k a₀ ∧ ∀ v ∈ latG V g,
      (finPart D e • finVec V v ∈ latGHat V (g * a₀) ↔
        finPart D e • finVec V v ∈ GlobalTheory.AdLat.hat D.host.F (M : Set (Fin V.rank → D.host.E))) := by
  intro D V P e ϖ k g M he hϖ1 hϖ2 hPM hMΛ hidx
  obtain ⟨v, π, s, h1, h2, h3, h4, h5⟩ := GlobalTheory.SplitCoord.exists_coord e he.1
  obtain ⟨B, hB⟩ := GlobalTheory.SplitLatBasis.exists_basis V e v π s he.1.1 h2 h3 h4
    (GlobalTheory.LatDual.lamHat_selfDual_and_module V).2
  obtain ⟨t, ht, hch⟩ := GlobalTheory.T.idempotent_part_completed_lattice_local_chart D V e v π s B he.1.1 h2 h3 h4 hB
  obtain ⟨hfg, hsp, -, -, hhat, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V g
  have hMfg : M.FG := by
    have hN : IsNoetherian (𝓞 D.host.E) (latG V g) := isNoetherian_of_fg_of_noetherian _ hfg
    have hc := (IsNoetherian.noetherian (M.comap (latG V g).subtype)).map (latG V g).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 hMΛ] at hc
  have hMsp : Submodule.span D.host.E (M : Set (Fin V.rank → D.host.E)) = ⊤ :=
    eq_top_iff.2 ((span_smul_top P _ hsp).symm.le.trans (Submodule.span_mono hPM))
  obtain ⟨C, hC⟩ := GlobalTheory.T.exists_local_matrix_chart_split_idempotent_completion D e v π s V.rank M he.1.1 h2 h3 h4 hMfg hMsp
  have hT : ∀ y : Fin V.rank → GlobalTheory.SplitPlace.RF D,
      finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (latG V g : Set (Fin V.rank → D.host.E)) ↔
      ∀ i, ((t • (GlobalTheory.SplitPlace.comp V π B g⁻¹ * B⁻¹).1) *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v := by
    intro y
    rw [← hhat, Units.val_mul]
    exact hch g y
  obtain ⟨Z, hZ1, hZ2, hZ3, hZM⟩ := GlobalTheory.T.exists_localHeckeMatrix_intermediateLattice D P e ϖ k V.rank v π s (latG V g) M t _ C he hϖ1 hϖ2
    h1 h2 h3 h4 h5 hfg hsp hPM hMΛ hidx ht hT hC
  obtain ⟨a₀, hsupp, hcomp⟩ := (GlobalTheory.SplitPlace.comp_bij (V := V) (B := B) he.1 h1 h2).1 Z
  have hu := GlobalTheory.SplitPlace.isUnif he h4 h5 ϖ hϖ1 hϖ2
  have hϖ0 := (GlobalTheory.SplitPlace.unif_facts hu).1
  refine ⟨a₀, (GlobalTheory.SplitPlace.hecke_iff he.1 h1 h2 h3 h4 hB hϖ0 k a₀).2 ⟨hsupp, ?_, ?_, ?_⟩, fun w _ => ?_⟩
  · rw [hcomp]; exact hZ1
  · rw [hcomp]; exact hZ2
  · rw [hcomp]; exact hZ3
  · rw [hch, hZM]
    have : (GlobalTheory.SplitPlace.comp V π B (g * a₀)⁻¹).1 = (Z⁻¹).1 * (GlobalTheory.SplitPlace.comp V π B g⁻¹).1 := by
      rw [mul_inv_rev, map_mul, map_inv, hcomp, Units.val_mul]
    rw [this, Units.val_mul, Matrix.mul_assoc, Matrix.mul_smul]

end GlobalTheory.HeckeLocLift
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.convolution_right_invariant_open : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {f : GA D V → ℂ}, f ∈ GlobalTheory.Orb.CcGA V → ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ, ∀ k ∈ U, k ∈ GfC V → ∀ g, GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) (g * k) = GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) g := by
  first | exact @GlobalTheory.ConvLevel.convR_level | exact GlobalTheory.ConvLevel.convR_level | (intros; apply GlobalTheory.ConvLevel.convR_level <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.testGridPlaceData_of_levelChoiceGrid : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc}, (∀ PP ∈ R.Pg, ∀ PP' ∈ R.Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') → PP = PP') → Formalism.L2.Host.SplitsCompletely {G'.pl.w G'.pl.v0} → (∀ k, GlobalTheory.ChiGrid.q0 D ≠ D.host.g k) → (GlobalTheory.ChiGrid.q0 D ≠ D.sp.T ∧ ∀ u : D.what₂.Word, GlobalTheory.ChiGrid.q0 D ≠ (D.mem u).A.T) → ∀ e : AE D, IsIdemSum e G'.pl.W0 → ∃ Z : GlobalTheory.Grid.PlaceDat D, Z.Is R.Pg R.Q e ∧ Z.q0 = GlobalTheory.ChiGrid.q0 D ∧ Z.w0 = G'.pl.w G'.pl.v0 ∧ Z.e0 = G'.pl.depth sc G'.pl.v0 ∧ Z.W R.Pg = G'.pl.W0 ∧ Z.ideal R.Pg = G'.modul ∧ Z.S0 R.Pg = G'.pl.S0 ∧ ∀ w, w ∈ R.Pg ∨ w ∈ Z.Wd → w.under (𝓞 D.host.F) ∈ GlobalTheory.ChiGrid.S1 D := by
  first | exact @GlobalTheory.GridJoin.placeDat_of_grid | exact GlobalTheory.GridJoin.placeDat_of_grid | (intros; apply GlobalTheory.GridJoin.placeDat_of_grid <;> assumption)
end
