module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.LiftFactorization
import GroundTheory.AutomorphicForms.MeasuresModulus
public import GroundTheory.AutomorphicForms.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
public import GroundTheory.AutomorphicForms.SmoothRep

@[expose] public section

section

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped Classical ENNReal

private theorem exists_eq_smul_id_of_irreducible {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] {n : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (GL (Fin n) E) X) (hs : IsSmooth ρ) (hi : ρ.IsIrreducible)
    (φ : X →ₗ[ℂ] X) (hφ : ∀ g x, φ (ρ g x) = ρ g (φ x)) : ∃ c : ℂ, φ = c • LinearMap.id := by
  haveI : ρ.IsIrreducible := hi
  obtain ⟨c, hc⟩ := (GroundTheory.Automorphic.algebraMap_intertwiningMap_bijective_of_isSmooth
      (show GroundTheory.Automorphic.IsSmooth ρ from hs)).2
    (⟨φ, fun g => LinearMap.ext fun x => hφ g x⟩ : Representation.IntertwiningMap ρ ρ)
  exact ⟨c, LinearMap.ext fun x =>
    (congrArg (fun f : Representation.IntertwiningMap ρ ρ => f x) hc).symm⟩


theorem UpperTheory.Gal.InertialTypesAlt.L.twScale :
    UpperTheory.Gal.InertialTypesAlt.L.TwScale := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hgen n V _ _ ρ hs hi I hI
  haveI := hi
  set m := Module.finrank k E with hm
  have hmpos : 0 < m := Module.finrank_pos
  have hiter : ∀ j : ℕ, ∀ g x, ((I : V →ₗ[ℂ] V) ^ j) (ρ g x) =
      ρ (GlobalTheory.LBC.galAct (σ ^ j) n g) (((I : V →ₗ[ℂ] V) ^ j) x) := by
    intro j
    induction j with
    | zero =>
      intro g x
      rw [pow_zero, pow_zero, GlobalTheory.LBC.galAct_one]
      rfl
    | succ j ih =>
      intro g x
      rw [pow_succ', pow_succ', GlobalTheory.LBC.galAct_mul, Module.End.mul_apply, Module.End.mul_apply, ih]
      exact hI _ _
  have hσm : σ ^ m = 1 := by
    rw [hm, ← IsGalois.card_aut_eq_finrank]
    exact pow_card_eq_one'
  obtain ⟨c, hc⟩ := exists_eq_smul_id_of_irreducible ρ hs hi ((I : V →ₗ[ℂ] V) ^ m) (by
    intro g x
    rw [hiter m g x, hσm, GlobalTheory.LBC.galAct_one]
    rfl)
  have hinj : Function.Injective ((I : V →ₗ[ℂ] V) ^ m) := by
    rw [Module.End.coe_pow]
    exact I.injective.iterate m
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := GroundTheory.Automorphic.exists_ne_zero_of_isIrreducible (ρ := ρ)
    apply hv
    apply hinj
    rw [hc, zero_smul, map_zero]
    rfl
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq c⁻¹ hmpos
  refine ⟨a, ?_, ?_, hmpos, ?_⟩
  · rintro rfl
    rw [zero_pow hmpos.ne'] at ha
    exact inv_ne_zero hc0 ha.symm
  · intro g
    ext x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, LinearEquiv.coe_coe]
    rw [hI]
  · rw [smul_pow, hc, ha, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rfl
end
end

section

noncomputable section

open MeasureTheory
open scoped Classical ENNReal

namespace UpperTheory.Gal.InertialTypesAlt.L

theorem avgInt : AvgInt := by
  intro G _ _ _ _ _ _ _ _ μ hμ K hKo hKc hK1 U hUo F hF q
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  set u : K → ℂ := fun y => F (q * (y : G)) with hu
  set S : Subgroup K := GlobalTheory.BCT.rStab u with hS
  have hUS : U.subgroupOf K ≤ S := by
    intro k hk
    have hk' : (k : G) ∈ U := Subgroup.mem_subgroupOf.mp hk
    show ∀ x : K, u (x * k) = u x
    intro x
    simp only [hu, Subgroup.coe_mul, ← mul_assoc]
    exact hF _ hk' _
  have hSo : IsOpen (S : Set K) := Subgroup.isOpen_mono hUS (Subgroup.subgroupOf_isOpen K U hUo)
  haveI : Finite (K ⧸ S) := Subgroup.quotient_finite_of_isOpen S hSo
  letI : Fintype (K ⧸ S) := Fintype.ofFinite _
  have hconst : ∀ y : K, u y = u (Quotient.out (QuotientGroup.mk y : K ⧸ S)) := by
    intro y
    have hmem : (Quotient.out (QuotientGroup.mk y : K ⧸ S))⁻¹ * y ∈ S := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    have h := hmem (Quotient.out (QuotientGroup.mk y : K ⧸ S))
    rw [mul_inv_cancel_left] at h
    exact h
  set S' : Set G := ((↑) : K → G) '' (S : Set K) with hS'
  have hS'o : IsOpen S' := hKo.isOpenMap_subtype_val _ hSo
  set A : K ⧸ S → Set G := fun c => (fun y => ((Quotient.out c : K) : G)⁻¹ * y) ⁻¹' S' with hA
  have hmemA : ∀ c y, y ∈ A c ↔ ∃ h : y ∈ K, (QuotientGroup.mk (⟨y, h⟩ : K) : K ⧸ S) = c := by
    intro c y
    simp only [hA, hS', Set.mem_preimage, Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨s, hs, hsy⟩
      have hy : y = ((Quotient.out c : K) : G) * (s : G) := by
        rw [hsy]
        group
      have hyK : y ∈ K := by
        rw [hy]
        exact K.mul_mem (Quotient.out c).2 s.2
      refine ⟨hyK, ?_⟩
      have he : (⟨y, hyK⟩ : K) = Quotient.out c * s := Subtype.ext hy
      rw [he]
      conv_rhs => rw [← QuotientGroup.out_eq' c]
      rw [QuotientGroup.eq]
      simpa [mul_assoc] using hs
    · rintro ⟨hyK, hc⟩
      have hmem : (Quotient.out c)⁻¹ * (⟨y, hyK⟩ : K) ∈ S := by
        rw [← QuotientGroup.eq, QuotientGroup.out_eq', hc]
      exact ⟨_, hmem, by simp⟩
  have hAm : ∀ c, MeasurableSet (A c) := fun c => (measurable_const_mul _) hS'o.measurableSet
  have hAK : ∀ c, A c ⊆ K := fun c y hy => ((hmemA c y).mp hy).1
  have hAμ : ∀ c, μ (A c) = μ S' := fun c => measure_preimage_mul μ _ S'
  have hunion : (⋃ c, A c) = (K : Set G) := by
    apply Set.Subset.antisymm (Set.iUnion_subset hAK)
    intro y hy
    exact Set.mem_iUnion.mpr ⟨_, (hmemA _ y).mpr ⟨hy, rfl⟩⟩
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro c c' hcc'
    refine Set.disjoint_left.mpr fun y h1 h2 => hcc' ?_
    obtain ⟨h, rfl⟩ := (hmemA c y).mp h1
    obtain ⟨h', rfl⟩ := (hmemA c' y).mp h2
    rfl
  have hsum : (Fintype.card (K ⧸ S) : ℝ≥0∞) * μ S' = 1 := by
    rw [← hK1, ← hunion, measure_iUnion hdisj hAm, tsum_fintype]
    simp only [hAμ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card (K ⧸ S) : ℕ) = S.index := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  have hreal : ∀ c, μ.real (A c) = ((S.index : ℝ))⁻¹ := by
    intro c
    have hne : (Fintype.card (K ⧸ S) : ℝ≥0∞) ≠ 0 := by
      simp
    have h1 : μ S' = ((Fintype.card (K ⧸ S) : ℝ≥0∞))⁻¹ := by
      rw [← ENNReal.eq_div_iff hne (by simp), ENNReal.div_eq_inv_mul, mul_one] at hsum
      exact hsum
    rw [Measure.real, hAμ, h1, ENNReal.toReal_inv, ENNReal.toReal_natCast, hcard]
  haveI : IsFiniteMeasure (μ.restrict (K : Set G)) :=
    ⟨by rw [Measure.restrict_apply_univ, hK1]; exact ENNReal.one_lt_top⟩
  have hint : ∫ y in (K : Set G), F (q * y) ∂μ =
      ∫ y in (K : Set G), ∑ c, (A c).indicator (fun _ => u (Quotient.out c)) y ∂μ := by
    refine setIntegral_congr_fun hKo.measurableSet fun y hy => ?_
    rw [Finset.sum_eq_single (QuotientGroup.mk (⟨y, hy⟩ : K) : K ⧸ S)]
    · rw [Set.indicator_of_mem ((hmemA _ y).mpr ⟨hy, rfl⟩)]
      exact hconst ⟨y, hy⟩
    · intro c _ hc
      refine Set.indicator_of_notMem (fun h => hc ?_) _
      obtain ⟨h', rfl⟩ := (hmemA c y).mp h
      rfl
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hint, integral_finsetSum _ fun c _ => (integrable_const _).indicator (hAm c)]
  unfold GlobalTheory.BCT.avg
  rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_indicator_const _ (hAm c), measureReal_restrict_apply (hAm c),
    Set.inter_eq_left.mpr (hAK c), hreal c, Complex.real_smul]
  push_cast
  rfl

end UpperTheory.Gal.InertialTypesAlt.L
end
end

section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UpperTheory.Gal.InertialTypesAlt.L

private lemma haar_measure_open_subgroup_index {T : Type} [Group T] [TopologicalSpace T] [IsTopologicalGroup T]
    [MeasurableSpace T] [BorelSpace T] (ν : Measure T) [ν.IsMulLeftInvariant]
    (C' H' : Subgroup T) (hH' : IsOpen (H' : Set T)) (hHC : H' ≤ C')
    [Finite (C' ⧸ H'.subgroupOf C')] :
    ν (C' : Set T) = (H'.relIndex C' : ℝ≥0∞) * ν (H' : Set T) := by
  classical
  haveI : Fintype (C' ⧸ H'.subgroupOf C') := Fintype.ofFinite _
  let r : (C' ⧸ H'.subgroupOf C') → T := fun q => ((Quotient.out q : C') : T)
  have hr : ∀ q, r q ∈ C' := fun q => (Quotient.out q).2
  have hcov : (C' : Set T) = ⋃ q, (fun y => (r q)⁻¹ * y) ⁻¹' (H' : Set T) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · intro hx
      refine ⟨QuotientGroup.mk ⟨x, hx⟩, ?_⟩
      have h1 := QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk ⟨x, hx⟩ : C' ⧸ H'.subgroupOf C'))
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at h1
      exact h1
    · rintro ⟨q, hq⟩
      have h2 := C'.mul_mem (hr q) (hHC hq)
      rwa [mul_inv_cancel_left] at h2
  have hdisj : Pairwise (Function.onFun Disjoint fun q => (fun y => (r q)⁻¹ * y) ⁻¹' (H' : Set T)) := by
    intro q q' hqq'
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    simp only [Set.mem_preimage, SetLike.mem_coe] at hx hx'
    apply hqq'
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq, Subgroup.mem_subgroupOf,
      Subgroup.coe_mul, Subgroup.coe_inv]
    change (r q)⁻¹ * r q' ∈ H'
    have e : (r q)⁻¹ * r q' = ((r q)⁻¹ * x) * ((r q')⁻¹ * x)⁻¹ := by group
    rw [e]
    exact H'.mul_mem hx (H'.inv_mem hx')
  rw [hcov, measure_iUnion hdisj (fun q => (hH'.preimage (continuous_const_mul _)).measurableSet), tsum_fintype]
  simp only [measure_preimage_mul]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  simp [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]

theorem volIdx :
    UpperTheory.Gal.InertialTypesAlt.L.VolIdx := by
  intro G _ _ _ _ _ _ T C H hT ν hν hCT hC hHC hH
  haveI := hν
  have eH : {t : T | (t : G) ∈ H} = ((H.subgroupOf T : Subgroup T) : Set T) := rfl
  have eC : {t : T | (t : G) ∈ C} = ((C.subgroupOf T : Subgroup T) : Set T) := rfl
  have hHo : IsOpen ((H.subgroupOf T : Subgroup T) : Set T) := by
    rw [← eH]
    exact hH
  have hCc : IsCompact ((C.subgroupOf T : Subgroup T) : Set T) := by
    rw [← eC]
    exact hT.isClosedEmbedding_subtypeVal.isCompact_preimage hC
  have hle : H.subgroupOf T ≤ C.subgroupOf T := fun x hx => hHC hx
  haveI : CompactSpace (C.subgroupOf T) := isCompact_iff_compactSpace.mp hCc
  haveI : Finite ((C.subgroupOf T) ⧸ (H.subgroupOf T).subgroupOf (C.subgroupOf T)) :=
    Subgroup.quotient_finite_of_isOpen _ (by
      rw [Subgroup.coe_subgroupOf]
      exact hHo.preimage continuous_subtype_val)
  have key := haar_measure_open_subgroup_index ν (C.subgroupOf T) (H.subgroupOf T) hHo hle
  rw [Subgroup.relIndex_subgroupOf hCT] at key
  have hpos : ν ((H.subgroupOf T : Subgroup T) : Set T) ≠ 0 :=
    (hHo.measure_pos ν ⟨1, (H.subgroupOf T).one_mem⟩).ne'
  have hfinH : ν ((H.subgroupOf T : Subgroup T) : Set T) ≠ ∞ :=
    ((measure_mono (fun x hx => hle hx)).trans_lt hCc.measure_lt_top).ne
  rw [eH, eC]
  refine ⟨?_, ?_⟩
  · rw [measureReal_def, ENNReal.toReal_ne_zero]
    exact ⟨hpos, hfinH⟩
  · simp only [measureReal_def, key, ENNReal.toReal_mul, ENNReal.toReal_natCast]

end UpperTheory.Gal.InertialTypesAlt.L
end
end

section

open MeasureTheory

private theorem cptConj_zpowers {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (j : H →* G) (hj : Topology.IsClosedEmbedding j) (t : H) :
    IsCompact (closure (Subgroup.zpowers (j t) : Set G)) ↔ IsCompact (closure (Subgroup.zpowers t : Set H)) := by
  have h1 : (Subgroup.zpowers (j t) : Set G) = j '' (Subgroup.zpowers t : Set H) := by
    rw [← MonoidHom.map_zpowers, Subgroup.coe_map]
  rw [h1, hj.closure_image_eq, hj.isInducing.isCompact_iff]

private theorem cptConj_conj {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (c : G) :
    Topology.IsClosedEmbedding (MulAut.conj c).toMonoidHom := by
  have e : ⇑(MulAut.conj c).toMonoidHom = ⇑((Homeomorph.mulRight c⁻¹).trans (Homeomorph.mulLeft c)) := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [e]
  exact Homeomorph.isClosedEmbedding _

private theorem cptConj_map {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] (j : H →* G) (hj : Topology.IsClosedEmbedding j)
    (S : Subgroup G) (T : Subgroup H) (h : G) (hST : ∀ x, x ∈ S ↔ ∃ t ∈ T, h⁻¹ * x * h = j t) :
    (GlobalTheory.BCT.cptPart S).map (MulAut.conj h⁻¹).toMonoidHom = (GlobalTheory.BCT.cptPart T).map j := by
  have hc := cptConj_conj h⁻¹
  have key : ∀ x : G, (MulAut.conj h⁻¹).toMonoidHom x = h⁻¹ * x * h := by
    intro x
    simp [MulAut.conj_apply]
  unfold GlobalTheory.BCT.cptPart
  rw [MonoidHom.map_closure, MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, ⟨hxS, hxc⟩, rfl⟩
    obtain ⟨t, htT, hxt⟩ := (hST x).mp hxS
    refine ⟨t, ⟨htT, ?_⟩, ?_⟩
    · rw [← cptConj_zpowers j hj, ← hxt, ← key, cptConj_zpowers _ hc]
      exact hxc
    · rw [key, hxt]
  · rintro ⟨t, ⟨htT, htc⟩, rfl⟩
    refine ⟨h * j t * h⁻¹, ⟨(hST _).mpr ⟨t, htT, by group⟩, ?_⟩, ?_⟩
    · rw [← cptConj_zpowers _ hc, key, show h⁻¹ * (h * j t * h⁻¹) * h = j t by group,
        cptConj_zpowers j hj]
      exact htc
    · rw [key]
      group

theorem UpperTheory.Gal.InertialTypesAlt.L.cptConj :
    UpperTheory.Gal.InertialTypesAlt.L.CptConj := by
  intro G H _ _ _ _ _ _ _ _ _ _ _ _ j hj S T h hST hcpt μ ν hμν
  have hmap := cptConj_map j hj S T h hST
  have hCm : MeasurableSet (((GlobalTheory.BCT.cptPart T).map j : Subgroup G) : Set G) := by
    rw [Subgroup.coe_map]
    exact (hcpt.image hj.continuous).isClosed.measurableSet
  have hf : Measurable (fun x : S => h⁻¹ * (x : G) * h) :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable.comp measurable_subtype_coe
  have hg : Measurable (fun t : T => j (t : H)) := hj.continuous.measurable.comp measurable_subtype_coe
  have h1 : {x : S | (x : G) ∈ GlobalTheory.BCT.cptPart S} =
      (fun x : S => h⁻¹ * (x : G) * h) ⁻¹' (((GlobalTheory.BCT.cptPart T).map j : Subgroup G) : Set G) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
    rw [← hmap, Subgroup.mem_map]
    constructor
    · intro hx
      exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
    · rintro ⟨y, hy, hyx⟩
      have hyx' : y = (x : G) := by
        simpa [MulAut.conj_apply] using hyx
      rwa [← hyx']
  have h2 : {t : T | (t : H) ∈ GlobalTheory.BCT.cptPart T} =
      (fun t : T => j (t : H)) ⁻¹' (((GlobalTheory.BCT.cptPart T).map j : Subgroup G) : Set G) := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
    exact (Subgroup.mem_map_iff_mem hj.injective).symm
  simp only [Measure.real]
  rw [h1, h2, ← Measure.map_apply hf hCm, ← Measure.map_apply hg hCm, hμν]
end
