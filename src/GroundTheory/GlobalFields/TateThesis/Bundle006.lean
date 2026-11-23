module

public import GroundTheory.GlobalFields.Adele.Bundle003
public import GroundTheory.GlobalFields.TateThesis.Bundle003
public import GroundTheory.GlobalFields.TateThesis.AdeleMeasurable
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import GroundTheory.GlobalFields.TateThesis.Bundle005
public import GroundTheory.GlobalFields.TateThesis.Bundle001
public import GroundTheory.GlobalFields.TateThesis.Conductor
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace GroundTheory.Global

open NumberField NumberField.mixedEmbedding IsDedekindDomain MeasureTheory Measure
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise Classical

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem countable_numberField : Countable K :=
  (Module.finBasis ℚ K).equivFun.toEquiv.countable_iff.2 inferInstance

instance sigmaCompactSpace_finiteAdeleRing : SigmaCompactSpace (FiniteAdeleRing (𝓞 K) K) := by
  have := countable_numberField K
  rw [← isSigmaCompact_univ_iff]
  have hU : (Set.univ : Set (FiniteAdeleRing (𝓞 K) K)) =
      ⋃ k : K, algebraMap K (FiniteAdeleRing (𝓞 K) K) k +ᵥ
        (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) := by
    refine (Set.eq_univ_of_forall fun a ↦ ?_).symm
    obtain ⟨k, hk⟩ := exists_sub_mem_integralFiniteAdeles a
    refine Set.mem_iUnion.2 ⟨k, ⟨a - algebraMap K _ k, hk, ?_⟩⟩
    simp
  rw [hU]
  exact isSigmaCompact_iUnion_of_isCompact _ fun k ↦
    (isCompact_integralFiniteAdeles K).vadd _

def integralFiniteAdelesPositiveCompacts : TopologicalSpace.PositiveCompacts (FiniteAdeleRing (𝓞 K) K) where
  carrier := integralFiniteAdeles (𝓞 K) K
  isCompact' := isCompact_integralFiniteAdeles K
  interior_nonempty' := by
    rw [isOpen_integralFiniteAdeles.interior_eq]
    exact ⟨0, Subring.zero_mem _⟩

theorem coe_integralFiniteAdelesPositiveCompacts :
    (integralFiniteAdelesPositiveCompacts K : Set (FiniteAdeleRing (𝓞 K) K)) =
      integralFiniteAdeles (𝓞 K) K :=
  rfl

def finiteAdeleMeasure : Measure (FiniteAdeleRing (𝓞 K) K) :=
  (NNReal.sqrt ‖discr K‖₊)⁻¹ • addHaarMeasure (integralFiniteAdelesPositiveCompacts K)

theorem sqrt_discr_ne_zero : NNReal.sqrt ‖discr K‖₊ ≠ 0 := by
  rw [Ne, NNReal.sqrt_eq_zero, nnnorm_eq_zero]
  exact discr_ne_zero K

instance : (finiteAdeleMeasure K).IsAddHaarMeasure := by
  rw [finiteAdeleMeasure]
  exact IsAddHaarMeasure.nnreal_smul _ (inv_ne_zero (sqrt_discr_ne_zero K))

instance : (finiteAdeleMeasure K).Regular := by
  rw [finiteAdeleMeasure]
  infer_instance

theorem finiteAdeleMeasure_integralFiniteAdeles :
    finiteAdeleMeasure K (integralFiniteAdeles (𝓞 K) K) = ((NNReal.sqrt ‖discr K‖₊)⁻¹ : ℝ≥0) := by
  rw [finiteAdeleMeasure, Measure.smul_apply, ← coe_integralFiniteAdelesPositiveCompacts,
    addHaarMeasure_self, ENNReal.smul_def, smul_eq_mul, mul_one]

def measurableEquivMixedSpace : InfiniteAdeleRing K ≃ᵐ mixedSpace K :=
  (homeomorphMixedSpace K).toMeasurableEquiv

theorem measurableEquivMixedSpace_apply (x : InfiniteAdeleRing K) :
    measurableEquivMixedSpace K x = homeomorphMixedSpace K x :=
  rfl

def addEquivMixedSpace : InfiniteAdeleRing K ≃+ mixedSpace K where
  __ := (homeomorphMixedSpace K).toEquiv
  map_add' x y := by
    change homeomorphMixedSpace K (x + y) = homeomorphMixedSpace K x + homeomorphMixedSpace K y
    simp only [homeomorphMixedSpace_apply, map_add (f := _)]

def infiniteAdeleMeasure : Measure (InfiniteAdeleRing K) :=
  (selfDualMeasure K).map (measurableEquivMixedSpace K).symm

instance : (infiniteAdeleMeasure K).IsAddHaarMeasure :=
  (addEquivMixedSpace K).symm.isAddHaarMeasure_map (selfDualMeasure K)
    (homeomorphMixedSpace K).symm.continuous (homeomorphMixedSpace K).continuous

theorem measurePreserving_measurableEquivMixedSpace :
    MeasurePreserving (measurableEquivMixedSpace K) (infiniteAdeleMeasure K) (selfDualMeasure K) :=
  MeasurePreserving.symm _ (⟨(measurableEquivMixedSpace K).symm.measurable, rfl⟩ :
    MeasurePreserving (measurableEquivMixedSpace K).symm (selfDualMeasure K) (infiniteAdeleMeasure K))

def adeleMeasure : Measure 𝔸[K] :=
  (infiniteAdeleMeasure K).prod (finiteAdeleMeasure K)

instance : (adeleMeasure K).IsAddHaarMeasure :=
  inferInstanceAs ((infiniteAdeleMeasure K).prod (finiteAdeleMeasure K)).IsAddHaarMeasure

theorem adeleMeasure_prod (A : Set (InfiniteAdeleRing K)) (B : Set (FiniteAdeleRing (𝓞 K) K)) :
    adeleMeasure K (A ×ˢ B) = infiniteAdeleMeasure K A * finiteAdeleMeasure K B :=
  Measure.prod_prod A B

theorem measurableSet_fundamentalSet : MeasurableSet (fundamentalSet K) :=
  ((homeomorphMixedSpace K).measurable (ZSpan.fundamentalDomain_measurableSet _)).prod
    isOpen_integralFiniteAdeles.measurableSet

theorem infiniteAdeleMeasure_fundamentalSetInfinite :
    infiniteAdeleMeasure K (fundamentalSetInfinite K) = (NNReal.sqrt ‖discr K‖₊ : ℝ≥0∞) := by
  change infiniteAdeleMeasure K ((measurableEquivMixedSpace K) ⁻¹'
    ZSpan.fundamentalDomain (latticeBasis K)) = _
  rw [(measurePreserving_measurableEquivMixedSpace K).measure_preimage_equiv, selfDualMeasure,
    Measure.smul_apply, volume_fundamentalDomain_latticeBasis, smul_eq_mul, ← mul_assoc, ← mul_pow,
    ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, one_mul]

theorem adeleMeasure_fundamentalSet : adeleMeasure K (fundamentalSet K) = 1 := by
  rw [fundamentalSet, adeleMeasure_prod, infiniteAdeleMeasure_fundamentalSetInfinite,
    finiteAdeleMeasure_integralFiniteAdeles, ← ENNReal.coe_mul,
    mul_inv_cancel₀ (sqrt_discr_ne_zero K), ENNReal.coe_one]

theorem isAddFundamentalDomain_fundamentalSet :
    IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 K) K) (fundamentalSet K)
      (adeleMeasure K) := by
  refine IsAddFundamentalDomain.mk' (measurableSet_fundamentalSet K).nullMeasurableSet fun x ↦ ?_
  obtain ⟨k, hk, huniq⟩ := existsUnique_sub_mem_fundamentalSet K x
  refine ⟨⟨algebraMap K 𝔸[K] (-k), -k, rfl⟩, ?_, ?_⟩
  · change algebraMap K 𝔸[K] (-k) + x ∈ fundamentalSet K
    rwa [map_neg, neg_add_eq_sub]
  · rintro ⟨_, k', rfl⟩ h
    change algebraMap K 𝔸[K] k' + x ∈ fundamentalSet K at h
    have hk' : -k' = k := huniq (-k') (by
      change x - algebraMap K 𝔸[K] (-k') ∈ fundamentalSet K
      rwa [map_neg, sub_neg_eq_add, add_comm])
    refine Subtype.ext ?_
    change algebraMap K 𝔸[K] k' = algebraMap K 𝔸[K] (-k)
    rw [← hk', neg_neg]

end

end GroundTheory.Global
end

section

namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical RealInnerProductSpace nonZeroDivisors

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

abbrev euclideanIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (euclidean.mixedSpace K) :=
  ZLattice.comap ℝ (idealLattice K I) (mixedToEuclidean K).symm.toLinearMap

abbrev euclideanConjIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (euclidean.mixedSpace K) :=
  ZLattice.comap ℝ (idealLattice K I) (mixedToEuclideanConj K).symm.toLinearMap

theorem mem_euclideanIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (u : euclidean.mixedSpace K) :
    u ∈ euclideanIdealLattice K I ↔ (mixedToEuclidean K).symm u ∈ idealLattice K I := Iff.rfl

theorem mem_euclideanConjIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (u : euclidean.mixedSpace K) :
    u ∈ euclideanConjIdealLattice K I ↔ (mixedToEuclideanConj K).symm u ∈ idealLattice K I :=
  Iff.rfl

theorem measurePreserving_mixedToEuclidean_symm :
    MeasurePreserving (mixedToEuclidean K).symm volume (selfDualMeasure K) := by
  have : MeasurePreserving (mixedToEuclidean K).toHomeomorph.toMeasurableEquiv
      (selfDualMeasure K) volume := measurePreserving_mixedToEuclidean K
  exact this.symm

theorem covolume_euclideanIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (euclideanIdealLattice K I) =
      FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) * √|(discr K : ℝ)| := by
  rw [ZLattice.covolume_comap (idealLattice K I) (selfDualMeasure K) volume
    (measurePreserving_mixedToEuclidean_symm K), covolume_idealLattice_selfDualMeasure]

theorem dualLattice_euclideanIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    dualLattice (euclideanIdealLattice K I) =
      euclideanConjIdealLattice K (traceDualIdeal K I) := by
  ext μ
  rw [mem_dualLattice, mem_euclideanConjIdealLattice, mem_idealLattice_traceDualIdeal_iff]
  constructor
  · intro h x hx
    obtain ⟨k, hk⟩ := h (mixedToEuclidean K x) (by
      rw [mem_euclideanIdealLattice, ContinuousLinearEquiv.symm_apply_apply]
      exact hx)
    refine ⟨k, ?_⟩
    rw [mixedTraceForm_comm, mixedTraceForm_eq_inner, ContinuousLinearEquiv.apply_symm_apply,
      real_inner_comm]
    exact hk
  · intro h ℓ hℓ
    obtain ⟨k, hk⟩ := h ((mixedToEuclidean K).symm ℓ) hℓ
    refine ⟨k, ?_⟩
    rw [← hk, mixedTraceForm_comm, mixedTraceForm_eq_inner, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply, real_inner_comm]

theorem inner_mixedToEuclideanConj_mixedToEuclidean (β a : mixedSpace K) :
    ⟪mixedToEuclideanConj K β, mixedToEuclidean K a⟫ = mixedTraceForm K β a := by
  rw [real_inner_comm, ← mixedTraceForm_eq_inner, mixedTraceForm_comm]

end

end GroundTheory.Global
end

section

open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing

namespace GroundTheory.Global

noncomputable section

section Ideals

variable {R : Type*} [CommRing R] [IsDedekindDomain R]


omit [IsDedekindDomain R] in
theorem asIdeal_pow_eq_one_iff (v : HeightOneSpectrum R) {k : ℕ} : v.asIdeal ^ k = 1 ↔ k = 0 := by
  constructor
  · intro h
    by_contra hk
    have hle : v.asIdeal ^ k ≤ v.asIdeal := Ideal.pow_le_self hk
    rw [h, Ideal.one_eq_top, top_le_iff] at hle
    exact v.isPrime.ne_top hle
  · rintro rfl
    exact pow_zero _

omit [IsDedekindDomain R] in
theorem mulSupport_asIdeal_pow (a : HeightOneSpectrum R → ℕ) :
    mulSupport (fun v : HeightOneSpectrum R ↦ v.asIdeal ^ a v) = support a := by
  ext v
  simp only [mem_mulSupport, mem_support, ne_eq, asIdeal_pow_eq_one_iff]

theorem finprod_asIdeal_pow_ne_bot (a : HeightOneSpectrum R → ℕ) :
    (∏ᶠ v : HeightOneSpectrum R, v.asIdeal ^ a v) ≠ ⊥ :=
  finprod_induction (fun I : Ideal R ↦ I ≠ ⊥) one_ne_zero (fun _ _ hx hy ↦ mul_ne_zero hx hy)
    fun v ↦ pow_ne_zero _ v.ne_bot

theorem finprod_asIdeal_pow_dvd_iff {a : HeightOneSpectrum R → ℕ} (ha : (support a).Finite)
    {I : Ideal R} (hI : I ≠ ⊥) :
    (∏ᶠ v : HeightOneSpectrum R, v.asIdeal ^ a v) ∣ I ↔
      ∀ v : HeightOneSpectrum R, a v ≤ multiplicity v.asIdeal I := by
  have hfa : HasFiniteMulSupport fun v : HeightOneSpectrum R ↦ v.asIdeal ^ a v := by
    rw [HasFiniteMulSupport, mulSupport_asIdeal_pow]
    exact ha
  constructor
  · intro h v
    have h1 : v.asIdeal ^ a v ∣ I := (finprod_mem_dvd v hfa).trans h
    have h2 := HeightOneSpectrum.multiplicity_le_of_ideal_ge v (Ideal.le_of_dvd h1) hI
    rwa [multiplicity_pow_self_of_prime (HeightOneSpectrum.prime v)] at h2
  · intro h
    have hm : HasFiniteMulSupport fun v : HeightOneSpectrum R ↦
        v.asIdeal ^ multiplicity v.asIdeal I := by
      simpa only [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity hI] using
        Ideal.hasFiniteMulSupport hI
    have hmb : HasFiniteMulSupport fun v : HeightOneSpectrum R ↦
        v.asIdeal ^ (multiplicity v.asIdeal I - a v) := by
      rw [HasFiniteMulSupport, mulSupport_asIdeal_pow] at hm ⊢
      refine hm.subset fun v hv ↦ ?_
      simp only [mem_support, ne_eq] at hv ⊢
      omega
    have hsplit : (fun v : HeightOneSpectrum R ↦ v.asIdeal ^ multiplicity v.asIdeal I) =
        fun v ↦ v.asIdeal ^ a v * v.asIdeal ^ (multiplicity v.asIdeal I - a v) :=
      funext fun v ↦ by rw [← pow_add, Nat.add_sub_cancel' (h v)]
    conv_rhs => rw [← Ideal.finprod_heightOneSpectrum_pow_multiplicity hI]
    rw [hsplit, finprod_mul_distrib hfa hmb]
    exact dvd_mul_right _ _

theorem asIdeal_dvd_finprod_iff {a : HeightOneSpectrum R → ℕ} (ha : (support a).Finite)
    (v : HeightOneSpectrum R) :
    v.asIdeal ∣ ∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ a w ↔ 1 ≤ a v := by
  have hfa : HasFiniteMulSupport fun v : HeightOneSpectrum R ↦ v.asIdeal ^ a v := by
    rw [HasFiniteMulSupport, mulSupport_asIdeal_pow]
    exact ha
  constructor
  · intro h
    classical
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := ha.toFinset)
      (by rw [mulSupport_asIdeal_pow, ha.coe_toFinset])] at h
    obtain ⟨w, hw, hvw⟩ := ((HeightOneSpectrum.prime v).dvd_finsetProd_iff _).1 h
    have hvw' := (HeightOneSpectrum.prime v).dvd_of_dvd_pow hvw
    have heq : v = w := HeightOneSpectrum.ext (associated_iff_eq.1
      ((HeightOneSpectrum.prime v).associated_of_dvd (HeightOneSpectrum.prime w) hvw'))
    subst heq
    rw [Set.Finite.mem_toFinset, mem_support] at hw
    omega
  · intro h
    exact (dvd_pow_self _ (by omega)).trans (finprod_mem_dvd v hfa)

end Ideals

namespace IdeleGroup

variable {K : Type*} [Field K] [NumberField K] {H : Type*} [Group H] [TopologicalSpace H]

def conductor (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H) : Ideal (𝓞 K) :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), v.asIdeal ^ conductorExponentAt χ v

omit [TopologicalSpace H] in
theorem conductor_ne_bot (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H) : conductor χ ≠ ⊥ :=
  finprod_asIdeal_pow_ne_bot _

def idealLevel (𝔪 : Ideal (𝓞 K)) : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ :=
  finiteLevel fun v ↦ multiplicity v.asIdeal 𝔪

theorem idealLevel_le_ker_iff (hH : NoSmallSubgroups H) (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H)
    (hχ : Continuous χ) {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    idealLevel 𝔪 ≤ χ.ker ↔ conductor χ ∣ 𝔪 := by
  rw [idealLevel, finiteLevel_le_ker_iff hH χ hχ, conductor,
    finprod_asIdeal_pow_dvd_iff (finite_support_conductorExponentAt hH χ hχ) h𝔪]

theorem dvd_conductor_iff (hH : NoSmallSubgroups H) (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H)
    (hχ : Continuous χ) (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal ∣ conductor χ ↔ 1 ≤ conductorExponentAt χ v :=
  asIdeal_dvd_finprod_iff (finite_support_conductorExponentAt hH χ hχ) v

theorem not_dvd_conductor_iff (hH : NoSmallSubgroups H) (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H)
    (hχ : Continuous χ) (v : HeightOneSpectrum (𝓞 K)) :
    ¬ v.asIdeal ∣ conductor χ ↔
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤
        (χ.comp (finiteUnitsSingle v)).ker := by
  rw [dvd_conductor_iff hH χ hχ, ← conductorExponentAt_eq_zero_iff hH χ hχ,
    Nat.one_le_iff_ne_zero, not_not]

def ofFinite : (FiniteAdeleRing (𝓞 K) K)ˣ →* IdeleGroup K :=
  (ContinuousMulEquiv.symm (prodEquiv K)).toMulEquiv.toMonoidHom.comp (MonoidHom.inr _ _)

theorem continuous_ofFinite : Continuous (ofFinite (K := K)) := by
  have : Continuous fun x : (FiniteAdeleRing (𝓞 K) K)ˣ ↦
      ContinuousMulEquiv.symm (prodEquiv K) ((1 : (InfiniteAdeleRing K)ˣ), x) :=
    (ContinuousMulEquiv.symm (prodEquiv K)).continuous.comp (continuous_const.prodMk continuous_id)
  exact this

@[simp]
theorem toFinite_ofFinite (x : (FiniteAdeleRing (𝓞 K) K)ˣ) : toFinite K (ofFinite x) = x := by
  change ((prodEquiv K) ((ContinuousMulEquiv.symm (prodEquiv K)) (1, x))).2 = x
  rw [ContinuousMulEquiv.apply_symm_apply]

@[simp]
theorem toInfinite_ofFinite (x : (FiniteAdeleRing (𝓞 K) K)ˣ) : toInfinite K (ofFinite x) = 1 := by
  change ((prodEquiv K) ((ContinuousMulEquiv.symm (prodEquiv K)) (1, x))).1 = 1
  rw [ContinuousMulEquiv.apply_symm_apply]

theorem mem_standardOpenSubgroup_iff_toFinite_mem (x : IdeleGroup K) :
    x ∈ standardOpenSubgroup K ↔ toFinite K x ∈ finiteLevel 0 := by
  rw [mem_standardOpenSubgroup, mem_finiteLevel]
  refine forall_congr' fun v ↦ ?_
  rw [Pi.zero_apply, unitsLevel_zero, Submonoid.mem_units_iff]
  rfl

theorem map_idealLevel_le_ker_iff (hH : NoSmallSubgroups H) (χ : IdeleGroup K →* H)
    (hχ : Continuous χ) {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    (idealLevel 𝔪).map ofFinite ≤ χ.ker ↔ conductor (χ.comp ofFinite) ∣ 𝔪 := by
  rw [Subgroup.map_le_iff_le_comap, MonoidHom.comap_ker]
  exact idealLevel_le_ker_iff hH _ (hχ.comp continuous_ofFinite) h𝔪

end IdeleGroup

end

end GroundTheory.Global
end
