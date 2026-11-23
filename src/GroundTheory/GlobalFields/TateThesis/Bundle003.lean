module

public import GroundTheory.GlobalFields.TateThesis.Bundle001
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import GroundTheory.GlobalFields.TateThesis.Bundle002
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Complex.Determinant
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace GroundTheory.Global

open Topology Filter IsDedekindDomain WithZero

noncomputable section

theorem exists_le_ker_of_noSmallSubgroups {G H : Type*} [Group G] [TopologicalSpace G] [Group H]
    [TopologicalSpace H] {P : Subgroup G → Prop}
    (hP : ∀ W ∈ 𝓝 (1 : G), ∃ L : Subgroup G, P L ∧ (L : Set G) ⊆ W) (hH : NoSmallSubgroups H)
    (χ : G →* H) (hχ : Continuous χ) : ∃ L : Subgroup G, P L ∧ L ≤ χ.ker := by
  obtain ⟨U, hU, hsmall⟩ := hH
  have hW : χ ⁻¹' U ∈ 𝓝 (1 : G) := hχ.continuousAt.preimage_mem_nhds (by rwa [map_one])
  obtain ⟨L, hL, hLW⟩ := hP _ hW
  refine ⟨L, hL, ?_⟩
  rw [← Subgroup.map_eq_bot_iff]
  refine hsmall _ ?_
  rintro _ ⟨x, hx, rfl⟩
  exact hLW hx

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

def unitsLevel (n : ℕ) : Subgroup (v.adicCompletion K)ˣ where
  carrier := {x | Valued.v (x : v.adicCompletion K) = 1 ∧
    Valued.v ((x : v.adicCompletion K) - 1) ≤ exp (-(n : ℤ))}
  one_mem' := by simp
  mul_mem' {x y} hx hy := by
    refine ⟨by simp [hx.1, hy.1], ?_⟩
    have : ((x * y : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1 =
        (x : v.adicCompletion K) * ((y : v.adicCompletion K) - 1) +
          ((x : v.adicCompletion K) - 1) := by
      push_cast; ring
    rw [this]
    refine Valuation.map_add_le _ ?_ hx.2
    rw [map_mul, hx.1, one_mul]
    exact hy.2
  inv_mem' {x} hx := by
    have hx0 : (x : v.adicCompletion K) ≠ 0 := x.ne_zero
    refine ⟨by simp [hx.1], ?_⟩
    have : ((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1 =
        (x : v.adicCompletion K)⁻¹ * (1 - (x : v.adicCompletion K)) := by
      rw [Units.val_inv_eq_inv_val, mul_sub, mul_one, inv_mul_cancel₀ hx0]
    rw [this, map_mul, map_inv₀, hx.1, inv_one, one_mul, Valuation.map_sub_swap]
    exact hx.2

variable {v} in
theorem mem_unitsLevel {n : ℕ} {x : (v.adicCompletion K)ˣ} :
    x ∈ unitsLevel v n ↔ Valued.v (x : v.adicCompletion K) = 1 ∧
      Valued.v ((x : v.adicCompletion K) - 1) ≤ exp (-(n : ℤ)) :=
  Iff.rfl


variable {v} in
theorem mem_unitsLevel_of_one_le {n : ℕ} (hn : 1 ≤ n) {x : (v.adicCompletion K)ˣ} :
    x ∈ unitsLevel v n ↔ Valued.v ((x : v.adicCompletion K) - 1) ≤ exp (-(n : ℤ)) := by
  refine ⟨And.right, fun h ↦ ⟨?_, h⟩⟩
  have hlt : Valued.v ((x : v.adicCompletion K) - 1) < Valued.v (1 : v.adicCompletion K) := by
    rw [map_one]
    refine h.trans_lt ?_
    rw [← exp_zero, exp_lt_exp]
    omega
  simpa using Valuation.map_eq_of_sub_lt _ hlt

theorem unitsLevel_zero :
    unitsLevel (K := K) v 0 = (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  ext x
  rw [Submonoid.mem_units_iff, mem_unitsLevel]
  change _ ↔ (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
    ((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
    Units.val_inv_eq_inv_val, map_inv₀]
  constructor
  · rintro ⟨h1, -⟩
    simp [h1]
  · rintro ⟨h1, h2⟩
    have hx0 : Valued.v (x : v.adicCompletion K) ≠ 0 := by simp
    have h3 : 1 ≤ Valued.v (x : v.adicCompletion K) := by
      exact (inv_le_one₀ (zero_lt_iff.2 hx0)).1 h2
    refine ⟨le_antisymm h1 h3, ?_⟩
    rw [Nat.cast_zero, neg_zero, exp_zero]
    exact Valuation.map_sub_le _ h1 (by simp)

theorem unitsLevel_antitone : Antitone (unitsLevel (K := K) v) := by
  intro m n hmn x hx
  refine ⟨hx.1, hx.2.trans ?_⟩
  rw [exp_le_exp]
  omega

theorem isOpen_unitsLevel (n : ℕ) : IsOpen (unitsLevel (K := K) v n : Set (v.adicCompletion K)ˣ) := by
  refine Subgroup.isOpen_of_mem_nhds (g := 1) _ ?_
  obtain ⟨a, ha⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective (K := K) (v := v)
    (exp (-(n : ℤ)))
  have ha0 : Valued.v a ≠ 0 := by simp [ha]
  have h1 : {y : v.adicCompletion K | Valued.v y = 1} ∈ 𝓝 (1 : v.adicCompletion K) := by
    simpa using Valued.locally_const (x := (1 : v.adicCompletion K)) (by simp)
  have h2 : {y : v.adicCompletion K | Valued.v (y - 1) ≤ exp (-(n : ℤ))} ∈
      𝓝 (1 : v.adicCompletion K) := by
    have hc : Continuous fun y : v.adicCompletion K ↦ y - 1 + a :=
      (continuous_id.sub continuous_const).add continuous_const
    have h := hc.continuousAt.preimage_mem_nhds (x := (1 : v.adicCompletion K))
      (by simpa using Valued.locally_const (x := a) ha0)
    refine Filter.mem_of_superset h fun y hy ↦ ?_
    have hy' : Valued.v (y - 1 + a) = exp (-(n : ℤ)) := by rw [← ha]; exact hy
    have : y - 1 = (y - 1 + a) - a := by ring
    change Valued.v (y - 1) ≤ exp (-(n : ℤ))
    rw [this]
    exact Valuation.map_sub_le _ hy'.le ha.le
  have h3 := Units.continuous_val.continuousAt.preimage_mem_nhds (x := (1 : (v.adicCompletion K)ˣ))
    (by rw [Units.val_one]; exact Filter.inter_mem h1 h2)
  exact Filter.mem_of_superset h3 fun x hx ↦ hx

theorem exists_unitsLevel_subset {t : Set (v.adicCompletion K)ˣ} (ht : t ∈ 𝓝 1) :
    ∃ n : ℕ, 1 ≤ n ∧ (unitsLevel (K := K) v n : Set (v.adicCompletion K)ˣ) ⊆ t := by
  rw [Units.isEmbedding_val₀.nhds_eq_comap, Units.val_one, mem_comap] at ht
  obtain ⟨t', ht', hsub⟩ := ht
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 ht'
  set c := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hc
  have hc0 : c ≠ 0 := fun h ↦ γ.ne_zero
    (MonoidWithZeroHom.ValueGroup₀.embedding_injective (h.trans (map_zero _).symm))
  refine ⟨(-(log c)).toNat + 1, by omega, fun x hx ↦ hsub (hγ ?_)⟩
  change Valued.v.restrict ((x : v.adicCompletion K) - 1) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding, ← hc]
  refine hx.2.trans_lt (lt_of_lt_of_eq ?_ (exp_log hc0))
  rw [exp_lt_exp]
  omega

section Character

variable {H : Type*} [Group H] [TopologicalSpace H]

theorem exists_unitsLevel_le_ker (hH : NoSmallSubgroups H) (χ : (v.adicCompletion K)ˣ →* H)
    (hχ : Continuous χ) : ∃ n : ℕ, 1 ≤ n ∧ unitsLevel v n ≤ χ.ker := by
  obtain ⟨L, ⟨n, hn, rfl⟩, hL⟩ := exists_le_ker_of_noSmallSubgroups
    (P := fun L ↦ ∃ n : ℕ, 1 ≤ n ∧ L = unitsLevel v n)
    (fun W hW ↦ by
      obtain ⟨n, hn, h⟩ := exists_unitsLevel_subset v hW
      exact ⟨_, ⟨n, hn, rfl⟩, h⟩) hH χ hχ
  exact ⟨n, hn, hL⟩

theorem isOpen_ker_of_continuous (hH : NoSmallSubgroups H) (χ : (v.adicCompletion K)ˣ →* H)
    (hχ : Continuous χ) : IsOpen (χ.ker : Set (v.adicCompletion K)ˣ) := by
  obtain ⟨n, -, hn⟩ := exists_unitsLevel_le_ker v hH χ hχ
  exact Subgroup.isOpen_mono hn (isOpen_unitsLevel v n)

def conductorExponent (χ : (v.adicCompletion K)ˣ →* H) : ℕ :=
  sInf {n : ℕ | unitsLevel v n ≤ χ.ker}

theorem unitsLevel_le_ker_iff (hH : NoSmallSubgroups H) (χ : (v.adicCompletion K)ˣ →* H)
    (hχ : Continuous χ) {n : ℕ} : unitsLevel v n ≤ χ.ker ↔ conductorExponent v χ ≤ n := by
  have hne : {n : ℕ | unitsLevel v n ≤ χ.ker}.Nonempty :=
    (exists_unitsLevel_le_ker v hH χ hχ).imp fun _ h ↦ h.2
  refine ⟨fun h ↦ Nat.sInf_le h, fun h ↦ (unitsLevel_antitone v h).trans (Nat.sInf_mem hne)⟩

theorem conductorExponent_eq_zero_iff (hH : NoSmallSubgroups H) (χ : (v.adicCompletion K)ˣ →* H)
    (hχ : Continuous χ) :
    conductorExponent v χ = 0 ↔ (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ χ.ker := by
  rw [← unitsLevel_zero, unitsLevel_le_ker_iff v hH χ hχ, Nat.le_zero]

end Character

end

end GroundTheory.Global
end

section

namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical ComplexConjugate RealInnerProductSpace FourierTransform Real ENNReal SchwartzMap

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def selfDualMeasure : Measure (mixedSpace K) := (2 ^ nrComplexPlaces K : ℝ≥0∞) • volume

instance : (selfDualMeasure K).IsAddHaarMeasure :=
  Measure.IsAddHaarMeasure.smul _ (by simp) (by simp)

def mapComplexCoord (a : ℂ ≃L[ℝ] ℂ) : mixedSpace K ≃L[ℝ] mixedSpace K :=
  (ContinuousLinearEquiv.refl ℝ _).prodCongr (ContinuousLinearEquiv.piCongrRight fun _ => a)

omit [NumberField K] in
theorem mapComplexCoord_apply (a : ℂ ≃L[ℝ] ℂ) (x : mixedSpace K) :
    mapComplexCoord K a x = (x.1, fun w => a (x.2 w)) := rfl

theorem det_mapComplexCoord (a : ℂ ≃L[ℝ] ℂ) :
    LinearMap.det (mapComplexCoord K a : mixedSpace K →ₗ[ℝ] mixedSpace K) =
      LinearMap.det (a : ℂ →ₗ[ℝ] ℂ) ^ nrComplexPlaces K := by
  have : (mapComplexCoord K a : mixedSpace K →ₗ[ℝ] mixedSpace K) =
      LinearMap.prodMap LinearMap.id
        (LinearMap.pi fun w => (a : ℂ →ₗ[ℝ] ℂ) ∘ₗ LinearMap.proj w) :=
    LinearMap.ext fun _ => rfl
  rw [this, LinearMap.det_prodMap, LinearMap.det_id, one_mul, LinearMap.det_pi,
    Finset.prod_const, Finset.card_univ]

theorem measurePreserving_mapComplexCoord (a : ℂ ≃L[ℝ] ℂ)
    (ha : |LinearMap.det (a : ℂ →ₗ[ℝ] ℂ)| = 2) :
    MeasurePreserving (mapComplexCoord K a) (selfDualMeasure K) volume := by
  refine ⟨(mapComplexCoord K a).continuous.measurable, ?_⟩
  have hd := det_mapComplexCoord K a
  have hne : LinearMap.det (mapComplexCoord K a : mixedSpace K →ₗ[ℝ] mixedSpace K) ≠ 0 := by
    rw [hd]
    refine pow_ne_zero _ fun h => ?_
    rw [h, abs_zero] at ha
    norm_num at ha
  have hmap : Measure.map (mapComplexCoord K a) (volume : Measure (mixedSpace K)) =
      ENNReal.ofReal |(LinearMap.det (mapComplexCoord K a : mixedSpace K →ₗ[ℝ] mixedSpace K))⁻¹| •
        (volume : Measure (mixedSpace K)) :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne
  rw [selfDualMeasure, Measure.map_smul _ (mapComplexCoord K a).continuous.aemeasurable,
    hmap, smul_smul, hd, abs_inv, abs_pow, ha,
    ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat, ENNReal.mul_inv_cancel (by simp) (by simp), one_smul]

def sqrtTwoSMulComplex : ℂ ≃L[ℝ] ℂ :=
  (LinearEquiv.smulOfNeZero ℝ ℂ (√2) (by positivity)).toContinuousLinearEquiv

theorem sqrtTwoSMulComplex_apply (z : ℂ) : sqrtTwoSMulComplex z = (√2 : ℝ) • z := rfl

theorem det_sqrtTwoSMulComplex : LinearMap.det (sqrtTwoSMulComplex : ℂ →ₗ[ℝ] ℂ) = 2 := by
  have : (sqrtTwoSMulComplex : ℂ →ₗ[ℝ] ℂ) = (√2 : ℝ) • LinearMap.id := LinearMap.ext fun _ => rfl
  rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one, Complex.finrank_real_complex,
    Real.sq_sqrt (by norm_num)]

def sqrtTwoSMulConj : ℂ ≃L[ℝ] ℂ := Complex.conjCLE.trans sqrtTwoSMulComplex

theorem sqrtTwoSMulConj_apply (z : ℂ) : sqrtTwoSMulConj z = (√2 : ℝ) • conj z := rfl

theorem det_sqrtTwoSMulConj : LinearMap.det (sqrtTwoSMulConj : ℂ →ₗ[ℝ] ℂ) = -2 := by
  have : (sqrtTwoSMulConj : ℂ →ₗ[ℝ] ℂ) =
      (sqrtTwoSMulComplex : ℂ →ₗ[ℝ] ℂ) ∘ₗ Complex.conjAe.toLinearEquiv.toLinearMap :=
    LinearMap.ext fun _ => rfl
  rw [this, LinearMap.det_comp, det_sqrtTwoSMulComplex, Complex.det_conjAe]
  norm_num

def mixedToEuclidean : mixedSpace K ≃L[ℝ] euclidean.mixedSpace K :=
  (mapComplexCoord K sqrtTwoSMulComplex).trans (euclidean.toMixed K).symm

def mixedToEuclideanConj : mixedSpace K ≃L[ℝ] euclidean.mixedSpace K :=
  (mapComplexCoord K sqrtTwoSMulConj).trans (euclidean.toMixed K).symm

theorem measurePreserving_mixedToEuclidean :
    MeasurePreserving (mixedToEuclidean K) (selfDualMeasure K) volume :=
  (euclidean.volumePreserving_toMixed_symm K).comp
    (measurePreserving_mapComplexCoord K _ (by rw [det_sqrtTwoSMulComplex]; norm_num))

theorem measurePreserving_mixedToEuclideanConj :
    MeasurePreserving (mixedToEuclideanConj K) (selfDualMeasure K) volume :=
  (euclidean.volumePreserving_toMixed_symm K).comp
    (measurePreserving_mapComplexCoord K _ (by rw [det_sqrtTwoSMulConj]; norm_num))

theorem inner_toMixed_symm (x y : mixedSpace K) :
    ⟪(euclidean.toMixed K).symm x, (euclidean.toMixed K).symm y⟫ =
      ∑ w, x.1 w * y.1 w + ∑ w, (conj (x.2 w) * y.2 w).re := by
  simp [euclidean.toMixed, PiLp.inner_apply, real_inner_eq_re_inner]
  congr 1 <;> exact Finset.sum_congr rfl fun w _ => by ring

theorem mixedTraceForm_eq_inner (x y : mixedSpace K) :
    mixedTraceForm K x y = ⟪mixedToEuclidean K x, mixedToEuclideanConj K y⟫ := by
  rw [mixedTraceForm_apply', mixedToEuclidean, mixedToEuclideanConj,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply, inner_toMixed_symm]
  simp only [mapComplexCoord_apply, sqrtTwoSMulComplex_apply, sqrtTwoSMulConj_apply]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  have hs : ((√2 : ℝ) : ℂ) * ((√2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have : conj ((√2 : ℝ) • x.2 w) * ((√2 : ℝ) • conj (y.2 w)) =
      ((√2 : ℝ) : ℂ) * ((√2 : ℝ) : ℂ) * conj (x.2 w * y.2 w) := by
    rw [Complex.real_smul, Complex.real_smul, map_mul, map_mul, Complex.conj_ofReal]
    ring
  rw [this, hs]
  simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def mixedFourier (f : mixedSpace K → E) : mixedSpace K → E :=
  VectorFourier.fourierIntegral 𝐞 (selfDualMeasure K) (mixedTraceForm K) f

def mixedFourierInv (f : mixedSpace K → E) : mixedSpace K → E :=
  VectorFourier.fourierIntegral 𝐞 (selfDualMeasure K) (-mixedTraceForm K) f

theorem mixedFourier_apply (f : mixedSpace K → E) (y : mixedSpace K) :
    mixedFourier K f y = ∫ x, 𝐞 (-mixedTraceForm K x y) • f x ∂selfDualMeasure K := rfl

theorem mixedFourierInv_apply (f : mixedSpace K → E) (x : mixedSpace K) :
    mixedFourierInv K f x = ∫ y, 𝐞 (mixedTraceForm K x y) • f y ∂selfDualMeasure K := by
  simp only [mixedFourierInv, VectorFourier.fourierIntegral, LinearMap.neg_apply, neg_neg,
    mixedTraceForm_comm K _ x]

theorem mixedFourier_eq (f : mixedSpace K → E) (y : mixedSpace K) :
    mixedFourier K f y = 𝓕 (f ∘ (mixedToEuclidean K).symm) (mixedToEuclideanConj K y) := by
  rw [mixedFourier_apply, Real.fourier_eq, ← (measurePreserving_mixedToEuclidean K).integral_comp
    (mixedToEuclidean K).toHomeomorph.measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [mixedTraceForm_eq_inner]

theorem mixedFourierInv_eq (f : mixedSpace K → E) (x : mixedSpace K) :
    mixedFourierInv K f x = 𝓕⁻ (f ∘ (mixedToEuclideanConj K).symm) (mixedToEuclidean K x) := by
  rw [mixedFourierInv_apply, Real.fourierInv_eq, ← (measurePreserving_mixedToEuclideanConj K).integral_comp
    (mixedToEuclideanConj K).toHomeomorph.measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [mixedTraceForm_eq_inner, real_inner_comm]

def mixedFourierSchwartz : 𝓢(mixedSpace K, E) →L[ℂ] 𝓢(mixedSpace K, E) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedToEuclideanConj K)).comp
    ((SchwartzMap.fourierTransformCLM ℂ).comp
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedToEuclidean K).symm))

theorem mixedFourierSchwartz_apply (f : 𝓢(mixedSpace K, E)) :
    ⇑(mixedFourierSchwartz K f) = mixedFourier K f := by
  funext y
  rw [mixedFourier_eq]
  rfl

variable [CompleteSpace E]

theorem mixedFourierInv_mixedFourier (f : 𝓢(mixedSpace K, E)) (x : mixedSpace K) :
    mixedFourierInv K (mixedFourier K f) x = f x := by
  set F : 𝓢(euclidean.mixedSpace K, E) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedToEuclidean K).symm f with hFdef
  have hF : (F : euclidean.mixedSpace K → E) = f ∘ (mixedToEuclidean K).symm := rfl
  have h1 : mixedFourier K f ∘ (mixedToEuclideanConj K).symm = 𝓕 (F : euclidean.mixedSpace K → E) := by
    funext v
    rw [Function.comp_apply, mixedFourier_eq, ContinuousLinearEquiv.apply_symm_apply, hF]
  have h2 : Integrable (𝓕 (F : euclidean.mixedSpace K → E)) := by
    rw [← SchwartzMap.fourier_coe]
    exact (𝓕 F).integrable
  rw [mixedFourierInv_eq, h1, F.continuous.fourierInv_fourier_eq F.integrable h2, hF,
    Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]

end

end GroundTheory.Global
end
