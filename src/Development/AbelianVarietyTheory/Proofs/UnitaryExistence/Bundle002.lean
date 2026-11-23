module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Smooth.Locus
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.Smooth.Field
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

section

namespace GlobalTheory.DedekindSmooth

open Polynomial IsLocalRing

theorem isSmoothAt_bot (k : Type) [Field k] [PerfectField k] (B : Type) [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] : Algebra.IsSmoothAt k (⊥ : Ideal B) := by
  have h : IsField (Localization.AtPrime (⊥ : Ideal B)) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal]
    simp
  letI := h.toField
  have : Algebra.EssFiniteType B (Localization.AtPrime (⊥ : Ideal B)) :=
    .of_isLocalization _ (⊥ : Ideal B).primeCompl
  have : Algebra.EssFiniteType k (Localization.AtPrime (⊥ : Ideal B)) := .comp _ B _
  exact Algebra.FormallySmooth.of_perfectField

theorem exists_uniformiser (B : Type) [CommRing B] [IsDedekindDomain B] (q : Ideal B) [q.IsPrime]
    (hq : q ≠ ⊥) : ∃ t ∈ q, t ≠ 0 ∧ maximalIdeal (Localization.AtPrime q) =
      Ideal.span {algebraMap B (Localization.AtPrime q) t} := by
  have := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hq
    (Localization.AtPrime q)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime q)
  obtain ⟨⟨t, s⟩, h⟩ := IsLocalization.surj q.primeCompl π
  have hs : IsUnit (algebraMap B (Localization.AtPrime q) s) := IsLocalization.map_units _ s
  have hm : maximalIdeal (Localization.AtPrime q) =
      Ideal.span {algebraMap B (Localization.AtPrime q) t} := by
    simp only at h
    rw [← h, Ideal.span_singleton_mul_right_unit hs, hπ.maximalIdeal_eq]
  refine ⟨t, ?_, ?_, hm⟩
  · rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q, hm]
    exact Ideal.mem_span_singleton_self _
  · rintro rfl
    simp only [map_zero] at h
    exact mul_ne_zero hπ.ne_zero hs.ne_zero h

theorem isSmoothAt_of_ne_bot (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B]
    [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : Ideal B) [hqp : q.IsPrime]
    (hq : q ≠ ⊥) : Algebra.IsSmoothAt k q := by
  obtain ⟨t, htq, ht0, hm⟩ := exists_uniformiser B q hq
  have hqm : q.IsMaximal := hqp.isMaximal hq
  have htr : Transcendental k t := by
    intro ha
    have hi := ha.isIntegral
    have hu : IsUnit t := hi.isUnit ht0
    exact hqp.ne_top (Ideal.eq_top_of_isUnit_mem _ htq hu)
  letI : Algebra k[X] B := (aeval t : k[X] →ₐ[k] B).toRingHom.toAlgebra
  have : IsScalarTower k k[X] B := .of_algebraMap_eq fun c => by
    change _ = aeval t (algebraMap k k[X] c)
    simp
  have hinj : Function.Injective (algebraMap k[X] B) := transcendental_iff_injective.mp htr
  have : FaithfulSMul k[X] B := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : Module.Flat k[X] B := inferInstance
  have : Algebra.FiniteType k[X] B := .of_restrictScalars_finiteType k _ _
  have : Algebra.FinitePresentation k[X] B :=
    (Algebra.FinitePresentation.of_finiteType (R := k[X]) (A := B)).mp ‹_›
  let p : Ideal k[X] := q.under k[X]
  letI := Localization.AtPrime.algebraOfLiesOver p q
  have hsep : Algebra.IsSeparable p.ResidueField q.ResidueField := by
    have : Module.Finite k (B ⧸ q) := by
      letI := Ideal.Quotient.field q
      exact finite_of_finite_type_of_isJacobsonRing k (B ⧸ q)
    have : Module.Finite k q.ResidueField :=
      Module.Finite.of_surjective (IsScalarTower.toAlgHom k (B ⧸ q) q.ResidueField).toLinearMap
        (Ideal.bijective_algebraMap_quotient_residueField q).2
    have : IsScalarTower k p.ResidueField q.ResidueField := .of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply k k[X] p.ResidueField,
        ← IsScalarTower.algebraMap_apply k[X] p.ResidueField q.ResidueField,
        ← IsScalarTower.algebraMap_apply]
    exact Algebra.isSeparable_tower_top_of_isSeparable k _ _
  have hmap : p.map (algebraMap k[X] (Localization.AtPrime q)) = maximalIdeal _ := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply k[X] B (Localization.AtPrime q),
        IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q]
      exact hx
    · have hX : algebraMap k[X] B X = t := aeval_X t
      rw [hm, Ideal.span_singleton_le_iff_mem, ← hX, ← IsScalarTower.algebraMap_apply]
      apply Ideal.mem_map_of_mem
      change algebraMap k[X] B X ∈ q
      rwa [hX]
  have : Algebra.IsUnramifiedAt k[X] q :=
    (Algebra.isUnramifiedAt_iff_map_eq k[X] p q).mpr ⟨hsep, hmap⟩
  have : Algebra.IsEtaleAt k[X] q := .of_isUnramifiedAt_of_flat q
  exact Algebra.FormallySmooth.comp k k[X] _

theorem smooth_of_isDedekindDomain :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [IsDedekindDomain B]
      [Algebra k B] [Algebra.FiniteType k B], Algebra.Smooth k B := by
  intro k _ _ B _ _ _ _
  have : Algebra.FinitePresentation k B :=
    (Algebra.FinitePresentation.of_finiteType (R := k) (A := B)).mp ‹_›
  refine ⟨Algebra.smoothLocus_eq_univ_iff.mp (Set.eq_univ_iff_forall.mpr fun q => ?_), ‹_›⟩
  obtain ⟨q, hq⟩ := q
  by_cases h : q = ⊥
  · subst h
    exact isSmoothAt_bot k B
  · exact isSmoothAt_of_ne_bot k B q h

end GlobalTheory.DedekindSmooth
end

section

open MeasureTheory Topology Matrix
open scoped ENNReal

namespace GlobalTheory

theorem map_restrict_subgroup_eq_smul_haar (G : Type) [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (H : Subgroup G) (hH : MeasurableSet (H : Set G)) (hμ : μ H ≠ 0)
    (R : Type) [Group R] [TopologicalSpace R] [IsTopologicalGroup R] [T2Space R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
    (ν : Measure R) [ν.IsHaarMeasure] (ψ : G →* R) (hψ : Measurable ψ)
    (hs : ∀ t, ∃ h ∈ H, ψ h = t) (hf : ∀ t, ∃ W ∈ 𝓝 t, μ ((H : Set G) ∩ ψ ⁻¹' W) ≠ ⊤) :
    ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ⊤ ∧ (μ.restrict H).map ψ = κ • ν ∧ ν.IsMulRightInvariant := by
  set m : Measure R := (μ.restrict H).map ψ with hm
  have happ : ∀ s, MeasurableSet s → m s = μ (ψ ⁻¹' s ∩ H) := by
    intro s hs'
    rw [hm, Measure.map_apply hψ hs', Measure.restrict_apply (hψ hs')]
  have hL : m.IsMulLeftInvariant := by
    rw [← forall_measure_preimage_mul_iff]
    intro t s hs'
    obtain ⟨h, hh, rfl⟩ := hs t
    rw [happ _ hs', happ _ (measurable_const_mul _ hs'), ← measure_preimage_mul μ h (ψ ⁻¹' s ∩ H)]
    congr 1
    ext g
    simp [H.mul_mem_cancel_left hh]
  have hR : m.IsMulRightInvariant := by
    rw [← forall_measure_preimage_mul_right_iff]
    intro t s hs'
    obtain ⟨h, hh, rfl⟩ := hs t
    rw [happ _ hs', happ _ (measurable_mul_const _ hs'),
      ← measure_preimage_mul_right μ h (ψ ⁻¹' s ∩ H)]
    congr 1
    ext g
    simp [H.mul_mem_cancel_right hh]
  have hF : IsLocallyFiniteMeasure m := by
    refine ⟨fun t => ?_⟩
    obtain ⟨W, hW, hW'⟩ := hf t
    refine ⟨interior W, interior_mem_nhds.2 hW, ?_⟩
    rw [happ _ isOpen_interior.measurableSet]
    refine lt_of_le_of_lt (measure_mono ?_) (lt_top_iff_ne_top.2 hW')
    intro g hg
    exact ⟨hg.2, interior_subset (s := W) hg.1⟩
  have h0 : m ≠ 0 := by
    intro h
    have := happ Set.univ MeasurableSet.univ
    rw [h] at this
    apply hμ
    simpa using this.symm
  have hκ := Measure.isMulLeftInvariant_eq_smul m ν
  set c := Measure.haarScalarFactor m ν
  have hc : c ≠ 0 := by
    intro h
    rw [h, zero_smul] at hκ
    exact h0 hκ
  have hc' : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc
  have hκ' : m = (c : ℝ≥0∞) • ν := hκ
  refine ⟨c, hc', ENNReal.coe_ne_top, hκ', ?_⟩
  have : ν = (c : ℝ≥0∞)⁻¹ • m := by
    rw [hκ', smul_smul, ENNReal.inv_mul_cancel hc' ENNReal.coe_ne_top, one_smul]
  rw [this]
  infer_instance

theorem map_restrict_subgroup_eq_common_smul_haar : ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (H : Subgroup G), MeasurableSet (H : Set G) → μ H ≠ 0 → ∀ (ι : Type) (R : ι → Type) [∀ k, Group (R k)] [∀ k, TopologicalSpace (R k)] [∀ k, IsTopologicalGroup (R k)] [∀ k, T2Space (R k)] [∀ k, LocallyCompactSpace (R k)] [∀ k, SecondCountableTopology (R k)] [∀ k, MeasurableSpace (R k)] [∀ k, BorelSpace (R k)] (ν : ∀ k, Measure (R k)) [∀ k, (ν k).IsHaarMeasure] (ψ : ∀ k, G →* R k), (∀ k, Measurable (ψ k)) → (∀ k t, ∃ h ∈ H, ψ k h = t) → (∀ k t, ∃ W ∈ 𝓝 t, μ ((H : Set G) ∩ ψ k ⁻¹' W) ≠ ⊤) → (∀ k k', ∃ (e : R k ≃ᵐ R k') (α : R k → R k) (u : R k), MeasurePreserving e (ν k) (ν k') ∧ Measurable α ∧ (∀ g, ψ k' g = e (α (ψ k g))) ∧ ∀ t, α (α t) = u⁻¹ * t * u) → ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ⊤ ∧ ∀ k, (μ.restrict H).map (ψ k) = κ • ν k := by
  intro G _ _ _ μ _ _ H hH hμ ι R _ _ _ _ _ _ _ _ ν _ ψ hψ hs hf hc
  choose κ h0 htop hκ hR using fun k =>
    map_restrict_subgroup_eq_smul_haar G μ H hH hμ (R k) (ν k) (ψ k) (hψ k) (hs k) (hf k)
  have key : ∀ k k', κ k = κ k' := by
    intro k k'
    obtain ⟨e, α, u, he, hα, hψe, hαα⟩ := hc k k'
    have := hR k
    have h1 : κ k' • ν k' = (κ k • (ν k).map α).map e := by
      rw [← hκ k', ← Measure.map_smul _ hα.aemeasurable, ← hκ k, Measure.map_map hα (hψ k),
        Measure.map_map e.measurable (hα.comp (hψ k))]
      congr 1
      funext g
      exact hψe g
    have h2 : κ k' • ν k = κ k • (ν k).map α := by
      have := congrArg (Measure.map e.symm) h1
      rw [Measure.map_smul _ e.symm.measurable.aemeasurable, (he.symm e).map_eq, MeasurableEquiv.map_symm_map] at this
      exact this
    have h3 : ((ν k).map α).map α = ν k := by
      rw [Measure.map_map hα hα]
      have : α ∘ α = (fun t => t * u) ∘ (fun t => u⁻¹ * t) := funext hαα
      rw [this, ← Measure.map_map (measurable_mul_const u) (measurable_const_mul u⁻¹),
        map_mul_left_eq_self, map_mul_right_eq_self]
    have h4 : κ k' • (ν k).map α = κ k • ν k := by
      have := congrArg (Measure.map α) h2
      rw [Measure.map_smul _ hα.aemeasurable, Measure.map_smul _ hα.aemeasurable, h3] at this
      exact this
    have h5 : (κ k' * κ k') • ν k = (κ k * κ k) • ν k := by
      rw [mul_smul, h2, smul_comm, h4, mul_smul]
    obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (R k)) := inferInstance
    have hK0 : ν k K ≠ 0 :=
      (Measure.measure_pos_of_nonempty_interior (ν k) K.interior_nonempty).ne'
    have hKt : ν k K ≠ ⊤ := K.isCompact.measure_ne_top
    have h6 := congrArg (fun m : Measure (R k) => m K) h5
    simp only [Measure.smul_apply, smul_eq_mul] at h6
    have h7 : κ k' * κ k' = κ k * κ k := (ENNReal.mul_left_inj hK0 hKt).1 h6
    rcases lt_trichotomy (κ k) (κ k') with h | h | h
    · exact absurd h7 (ENNReal.mul_lt_mul h h).ne'
    · exact h
    · exact absurd h7 (ENNReal.mul_lt_mul h h).ne
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨k₀⟩⟩
  · exact ⟨1, one_ne_zero, ENNReal.one_ne_top, fun k => hι.elim k⟩
  · exact ⟨κ k₀, h0 k₀, htop k₀, fun k => by rw [hκ k, key k k₀]⟩

end GlobalTheory
end

section

open IsLocalRing NumberField IsDedekindDomain

namespace GlobalTheory


open IsLocalRing IsDedekindDomain NumberField in
theorem _root_.GlobalTheory.isDiscreteValuationRing_and_finite_residueField_valuationSubringAtPrime
    {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] (v : IsDedekindDomain.HeightOneSpectrum R)
    (hfin : Finite (R ⧸ v.asIdeal)) :
      IsDiscreteValuationRing ↥(IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v) ∧
        Finite (IsLocalRing.ResidueField
          ↥(IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v)) := by
  let S := Localization.subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : IsLocalization.AtPrime S v.asIdeal := Localization.subalgebra.isLocalization_ofField K _ _
  have hD : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R v.ne_bot S
  haveI : IsLocalRing S := inferInstance
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  have hS : Finite (ResidueField S) :=
    Finite.of_equiv _ (IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal S).toEquiv
  exact ⟨hD, hS⟩

open IsLocalRing IsDedekindDomain NumberField in
private theorem eq_of_le_of_mem_nonunits_of_dvr {K : Type*} [Field K]
    (A W : ValuationSubring K) (h : A ≤ W) [IsDiscreteValuationRing A]
    (a : A) (ha0 : a ≠ 0) (haW : (a : K) ∈ W.nonunits) : A = W := by
  have hmem : ∀ (B : ValuationSubring K) (hB : A ≤ B) (x : A),
      x ∈ A.idealOfLE B hB ↔ (x : K) ∈ B.nonunits := by
    intro B hB x
    rw [ValuationSubring.mem_nonunits_iff]
    unfold ValuationSubring.idealOfLE
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
    rfl
  have hmax : ∀ (B : ValuationSubring K) (hB : A ≤ B), (a : K) ∈ B.nonunits →
      A.idealOfLE B hB = maximalIdeal A := by
    intro B hB haB
    have hne : A.idealOfLE B hB ≠ ⊥ := by
      intro hbot
      have : a ∈ A.idealOfLE B hB := (hmem B hB a).2 haB
      rw [hbot, Ideal.mem_bot] at this
      exact ha0 this
    have := (inferInstance : (A.idealOfLE B hB).IsPrime).isMaximal hne
    exact IsLocalRing.eq_maximalIdeal this
  have haA : (a : K) ∈ A.nonunits := (ValuationSubring.nonunits_le_nonunits.2 h) haW
  have hcongr : ∀ (P Q : Ideal A) [P.IsPrime] [Q.IsPrime], P = Q → A.ofPrime P = A.ofPrime Q := by
    rintro P Q _ _ rfl; rfl
  calc A = A.ofPrime (A.idealOfLE A le_rfl) := (A.ofPrime_idealOfLE A le_rfl).symm
    _ = A.ofPrime (A.idealOfLE W h) := hcongr _ _ ((hmax A le_rfl haA).trans (hmax W h haW).symm)
    _ = W := A.ofPrime_idealOfLE W h


open IsLocalRing IsDedekindDomain NumberField in
theorem _root_.GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField {L : Type*} [Field L]
    [NumberField L] (W : ValuationSubring L) {n : ℕ} (hn : n ≠ (0 : ℕ))
    (hW : (↑n : L) ∈ W.nonunits) :
      IsDiscreteValuationRing ↥W ∧ Finite (IsLocalRing.ResidueField ↥W) := by
  have hnW := hW
  have hint : ∀ x : 𝓞 L, algebraMap (𝓞 L) L x ∈ W := by
    intro x
    have h : IsIntegral W (x : L) := (RingOfIntegers.isIntegral_coe x).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
    show (x : L) ∈ W
    rw [← hy]; exact y.2
  let f : 𝓞 L →+* W := (algebraMap (𝓞 L) L).codRestrict W hint
  have hf : ∀ x : 𝓞 L, ((f x : W) : L) = (x : L) := fun x => rfl
  let P : Ideal (𝓞 L) := (maximalIdeal W).comap f
  have hPmem : ∀ x : 𝓞 L, x ∈ P ↔ (x : L) ∈ W.nonunits := by
    intro x
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff, ValuationSubring.mem_nonunits_iff, hf]
  have hnP : (n : 𝓞 L) ∈ P := by
    rw [hPmem]; simpa using hnW
  have hPne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Ideal.mem_bot] at hnP
    exact hn (by exact_mod_cast hnP)
  let v : HeightOneSpectrum (𝓞 L) := ⟨P, Ideal.comap_isPrime f (maximalIdeal W), hPne⟩
  have hfin : Finite (𝓞 L ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ hPne
  let A := HeightOneSpectrum.valuationSubringAtPrime L v
  have hAW : A ≤ W := by
    intro x hx
    let S := Localization.subalgebra.ofField L _ v.asIdeal.primeCompl_le_nonZeroDivisors
    haveI : IsLocalization.AtPrime S v.asIdeal := Localization.subalgebra.isLocalization_ofField L _ _
    obtain ⟨⟨a, s⟩, hy⟩ := IsLocalization.mk'_surjective v.asIdeal.primeCompl (⟨x, hx⟩ : S)
    have hspec := congrArg Subtype.val (IsLocalization.mk'_spec S a s)
    simp only at hy
    rw [hy] at hspec
    change x * ((s : 𝓞 L) : L) = (a : L) at hspec
    have hsu : IsUnit (f s) := by
      by_contra hns
      exact s.2 (show (s : 𝓞 L) ∈ P from (IsLocalRing.mem_maximalIdeal _).2 hns)
    obtain ⟨t, ht⟩ := hsu.exists_right_inv
    have h1 : ((s : 𝓞 L) : L) * (t : L) = 1 := by
      rw [← hf]; exact congrArg Subtype.val ht
    have hx' : x = (a : L) * (t : L) := by
      calc x = x * (((s : 𝓞 L) : L) * (t : L)) := by rw [h1, mul_one]
        _ = (a : L) * (t : L) := by rw [← mul_assoc, hspec]
    rw [hx']
    exact mul_mem (hint a) t.2
  obtain ⟨hD, hF⟩ :=
    _root_.GlobalTheory.isDiscreteValuationRing_and_finite_residueField_valuationSubringAtPrime L v hfin
  have hnA : (n : L) ∈ A := natCast_mem A n
  have heq : A = W := eq_of_le_of_mem_nonunits_of_dvr A W hAW ⟨(n : L), hnA⟩
    (by
      intro h0
      have := congrArg Subtype.val h0
      simp only [ZeroMemClass.coe_zero] at this
      exact hn (by exact_mod_cast this)) hnW
  rw [← heq]
  exact ⟨hD, hF⟩

end GlobalTheory
end

section

open IsDedekindDomain NumberField Filter Topology

namespace GlobalTheory.LocalNormBound

theorem local_bound (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (W : Set (v.adicCompletion F)) (hW : W ∈ 𝓝 (0 : v.adicCompletion F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ v.adicCompletionIntegers F, N • x ∈ W := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hW
  have hp : 0 < Ideal.absNorm v.asIdeal :=
    Nat.pos_of_ne_zero (fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h))
  set p := Ideal.absNorm v.asIdeal with hpdef
  have hlt : Valued.v ((p : ℕ) : v.adicCompletion F) < 1 := by
    have h1 : ((p : ℕ) : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (p : 𝓞 F)) := by
      simp
    rw [h1]
    have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap (𝓞 F) F (p : 𝓞 F))
    have h3 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (p : 𝓞 F)).2 (Ideal.absNorm_mem _)
    exact h2 ▸ h3
  have ht := Valued.tendsto_zero_pow_of_v_lt_one hlt
  have hS := Valued.mem_nhds_zero.2 ⟨γ, subset_rfl (a := _)⟩
  obtain ⟨n, hn⟩ := (ht.eventually hS).exists
  refine ⟨p ^ n, pow_pos hp n, fun x hx => hγ ?_⟩
  refine lt_of_le_of_lt ?_ hn
  rw [Valuation.restrict_le_iff, nsmul_eq_mul, map_mul, Nat.cast_pow]
  exact mul_le_of_le_one_right' hx

theorem main : ∀ (F : Type) [inst : Field F] [inst_1 : NumberField F], ∀ U ∈ nhds (0 : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F), ∃ (N : ℕ), (0 : ℕ) < N ∧ ∀ (a : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F), (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), (a : (a : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) → IsDedekindDomain.HeightOneSpectrum.adicCompletion F a) v ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v) → N • a ∈ U := by
  intro F _ _ U hU
  classical
  let φ : (Π v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F : Set (v.adicCompletion F))) →
      FiniteAdeleRing (𝓞 F) F :=
    RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite
  have hφ : Continuous φ := RestrictedProduct.isEmbedding_structureMap.continuous
  let z : Π v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => ⟨0, zero_mem _⟩
  have hz : φ z = 0 := FiniteAdeleRing.ext F fun v => rfl
  have h1 : φ ⁻¹' U ∈ 𝓝 z := hφ.continuousAt.preimage_mem_nhds (hz ▸ hU)
  rw [nhds_pi, Filter.mem_pi] at h1
  obtain ⟨I, hI, t, ht, hsub⟩ := h1
  have h2 : ∀ v : HeightOneSpectrum (𝓞 F), ∃ N : ℕ, 0 < N ∧
      ∀ x (hx : x ∈ v.adicCompletionIntegers F), ⟨N • x, nsmul_mem hx N⟩ ∈ t v := by
    intro v
    obtain ⟨W, hW, hWt⟩ := (mem_nhds_subtype _ _ _).1 (ht v)
    obtain ⟨N, hN, h⟩ := local_bound F v W hW
    exact ⟨N, hN, fun x hx => hWt (h x hx)⟩
  choose n hn hnt using h2
  refine ⟨∏ v ∈ hI.toFinset, n v, Finset.prod_pos fun v _ => hn v, fun a ha => ?_⟩
  set N := ∏ v ∈ hI.toFinset, n v with hN
  have h3 : φ (fun v => ⟨N • a v, nsmul_mem (ha v) N⟩) = N • a :=
    FiniteAdeleRing.ext F fun v => rfl
  rw [← h3]
  refine hsub fun v hv => ?_
  obtain ⟨k, hk⟩ : n v ∣ N := Finset.dvd_prod_of_mem _ (hI.mem_toFinset.2 hv)
  have h4 := hnt v (k • a v) (nsmul_mem (ha v) k)
  convert h4 using 2
  rw [hk, mul_smul]

end GlobalTheory.LocalNormBound
end

section

namespace GlobalTheory.IntegralOpen

open IsDedekindDomain NumberField

theorem isOpen_integral (F : Type) [Field F] [NumberField F] :
    IsOpen {a : FiniteAdeleRing (RingOfIntegers F) F |
      ∀ v : HeightOneSpectrum (RingOfIntegers F),
        (a : (w : HeightOneSpectrum (RingOfIntegers F)) → HeightOneSpectrum.adicCompletion F w) v ∈
          HeightOneSpectrum.adicCompletionIntegers F v} :=
  RestrictedProduct.isOpen_forall_mem
    (R := fun w : HeightOneSpectrum (RingOfIntegers F) => HeightOneSpectrum.adicCompletion F w)
    (A := fun w => (HeightOneSpectrum.adicCompletionIntegers F w : Set (HeightOneSpectrum.adicCompletion F w)))
    (fun _ => Valued.isOpen_valuationSubring _)

end GlobalTheory.IntegralOpen
end
