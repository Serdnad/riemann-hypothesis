module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Aesop.Main
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle192
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle195
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CellInt

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

def dcos (R K : Subgroup G) (q : G) : Set G := {g | ∃ r ∈ R, ∃ k ∈ K, g = r * q * k}

theorem dcos_eq_of_mem {R K : Subgroup G} {q h : G} (hh : h ∈ dcos R K q) : dcos R K h = dcos R K q := by
  obtain ⟨r, hr, k, hk, rfl⟩ := hh
  ext g
  constructor
  · rintro ⟨r', hr', k', hk', rfl⟩
    exact ⟨r' * r, R.mul_mem hr' hr, k * k', K.mul_mem hk hk', by group⟩
  · rintro ⟨r', hr', k', hk', rfl⟩
    exact ⟨r' * r⁻¹, R.mul_mem hr' (R.inv_mem hr), k⁻¹ * k', K.mul_mem (K.inv_mem hk) hk', by group⟩

def cellSet (R K : Subgroup G) (q h : G) : Set R := {r | q⁻¹ * ((r : G) * h) ∈ K}

theorem isOpen_cellSet {R K : Subgroup G} (hK : IsOpen (K : Set G)) (q h : G) : IsOpen (cellSet R K q h) :=
  (continuous_const.mul (continuous_subtype_val.mul continuous_const)).isOpen_preimage _ hK

theorem isCompact_cellSet {R K : Subgroup G} (hR : IsClosed (R : Set G)) (hK : IsCompact (K : Set G)) (q h : G) :
    IsCompact (cellSet R K q h) := by
  have h1 : IsCompact ((fun x : G => q⁻¹ * (x * h)) ⁻¹' (K : Set G)) :=
    ((Homeomorph.mulRight h).trans (Homeomorph.mulLeft q⁻¹)).isCompact_preimage.2 hK
  exact hR.isClosedEmbedding_subtypeVal.isCompact_preimage h1

theorem cellSet_of_mem {R K : Subgroup G} {q h : G} (r0 : R) (k0 : G) (hk0 : k0 ∈ K) (hh : h = r0 * q * k0) :
    cellSet R K q h = (fun r => r * r0) ⁻¹' cellSet R K q q := by
  ext r
  simp only [cellSet, Set.mem_preimage, Set.mem_setOf_eq, Subgroup.coe_mul, hh]
  constructor
  · intro hr
    have := K.mul_mem hr (K.inv_mem hk0)
    convert this using 1; group
  · intro hr
    have := K.mul_mem hr hk0
    convert this using 1; group

theorem cellSet_eq_empty {R K : Subgroup G} {q h : G} (hh : h ∉ dcos R K q) : cellSet R K q h = ∅ :=
  Set.eq_empty_of_forall_notMem fun r hr =>
    hh ⟨(r : G)⁻¹, R.inv_mem r.2, q⁻¹ * ((r : G) * h), hr, by group⟩


open Classical in
theorem isQuotientIntegral_indicator_doubleCoset (R K : Subgroup G) (hR : IsClosed (R : Set G)) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) (ρ : Measure R) (μ : Measure G) [ρ.IsHaarMeasure] [ρ.IsInvInvariant]
    [μ.IsHaarMeasure] (q : G) :
    IsQuotIntL1 ρ μ (fun g => if g ∈ dcos R K q then 1 else 0)
      (((μ (K : Set G)).toReal / (ρ (cellSet R K q q)).toReal : ℝ) : ℂ) := by
  classical
  have hRI : ρ.IsMulRightInvariant := by rw [← Measure.inv_eq_self ρ]; infer_instance
  set c : ℂ := ((((ρ (cellSet R K q q)).toReal)⁻¹ : ℝ) : ℂ) with hc
  set A : Set G := (fun x => q⁻¹ * x) ⁻¹' (K : Set G) with hA
  have hAo : IsOpen A := (continuous_const.mul continuous_id).isOpen_preimage _ hKo
  have hAc : IsCompact A := (Homeomorph.mulLeft q⁻¹).isCompact_preimage.2 hKc
  have hAμ : μ A = μ K := measure_preimage_mul μ q⁻¹ _
  have hS0 : ρ (cellSet R K q q) ≠ 0 := (isOpen_cellSet hKo q q).measure_ne_zero ρ ⟨1, by simp [cellSet]⟩
  have hSt : ρ (cellSet R K q q) ≠ ⊤ := ((isCompact_cellSet hR hKc q q).measure_lt_top (μ := ρ)).ne
  have e : ∀ h, (fun r : R => A.indicator (fun _ => c) ((r : G) * h)) = (cellSet R K q h).indicator fun _ => c := by
    intro h; funext r; simp only [Set.indicator_apply, hA, cellSet, Set.mem_preimage, Set.mem_setOf_eq, SetLike.mem_coe]
  refine ⟨A.indicator fun _ => c, ?_, fun h => ?_, fun h => ?_, ?_⟩
  · exact (integrableOn_const hAc.measure_lt_top.ne).integrable_indicator hAo.measurableSet
  · rw [e h]
    exact (integrableOn_const ((isCompact_cellSet hR hKc q h).measure_lt_top (μ := ρ)).ne).integrable_indicator
      (isOpen_cellSet hKo q h).measurableSet
  · rw [e h, integral_indicator (isOpen_cellSet hKo q h).measurableSet, setIntegral_const]
    show (if h ∈ dcos R K q then (1 : ℂ) else 0) = ρ.real (cellSet R K q h) • c
    by_cases hh : h ∈ dcos R K q
    · rw [if_pos hh]
      obtain ⟨r0, hr0, k0, hk0, rfl⟩ := hh
      rw [cellSet_of_mem ⟨r0, hr0⟩ k0 hk0 rfl, measureReal_def, measure_preimage_mul_right, hc, Complex.real_smul,
        ← Complex.ofReal_mul, mul_inv_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨hS0, hSt⟩), Complex.ofReal_one]
    · rw [if_neg hh, cellSet_eq_empty hh]
      simp
  · rw [integral_indicator hAo.measurableSet, setIntegral_const, measureReal_def, hAμ, hc, Complex.real_smul, ← Complex.ofReal_mul, div_eq_mul_inv]

theorem quotient_integral_finset_sum {R : Subgroup G} {ρ : Measure R} {μ : Measure G} {ι : Type} (s : Finset ι)
    (g : ι → G → ℂ) (z : ι → ℂ) (hs : ∀ i ∈ s, IsQuotIntL1 ρ μ (g i) (z i)) :
    IsQuotIntL1 ρ μ (fun h => ∑ i ∈ s, g i h) (∑ i ∈ s, z i) := by
  classical
  revert hs
  refine Finset.induction_on s ?_ ?_
  · intro _
    have e : (fun h => ∑ i ∈ (∅ : Finset ι), g i h) = 0 := by funext h; simp
    rw [e, Finset.sum_empty]
    exact IsQuotIntL1.zero
  · intro a s ha ih hs
    have := (hs a (Finset.mem_insert_self a s)).add (ih fun i hi => hs i (Finset.mem_insert_of_mem hi))
    rw [Finset.sum_insert ha]
    convert this using 1
    funext h
    simp [Finset.sum_insert ha]

end GlobalTheory.CellInt


open GlobalTheory.CellInt in
theorem GlobalTheory.CellInt.quotInt_finiteCells : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (R K : Subgroup G), IsClosed (R : Set G) → IsCompact (K : Set G) → IsOpen (K : Set G) → ∀ (ρ : Measure R) (μ : Measure G), ρ.IsHaarMeasure → ρ.IsInvInvariant → μ.IsHaarMeasure → μ.IsMulRightInvariant → ∀ T : Finset G, ∃ (T' : Finset G) (w : G → ℂ), T' ⊆ T ∧ ∀ f : G → ℂ, (∀ r ∈ R, ∀ g, f (r * g) = f g) → (∀ k ∈ K, ∀ g, f (g * k) = f g) → (∀ g, f g ≠ 0 → ∃ q ∈ T, ∃ r ∈ R, ∃ k ∈ K, g = r * q * k) → IsQuotIntL1 ρ μ f (∑ q ∈ T', w q * f q) := by
  intro G _ _ _ _ _ _ _ _ R K hR hKc hKo ρ μ hρ hρi hμ hμr T
  classical
  obtain ⟨u, hus, hinj, himg⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn (f := dcos R K) (T : Set G)
    (T.image (dcos R K)) (by rw [Finset.coe_image]; exact Set.surjOn_image _ _)
  refine ⟨u, fun q => (((μ (K : Set G)).toReal / (ρ (cellSet R K q q)).toReal : ℝ) : ℂ), Finset.coe_subset.1 hus,
    fun f hfR hfK hsupp => ?_⟩
  have hinv : ∀ q h, h ∈ dcos R K q → f h = f q := by
    rintro q h ⟨r, hr, k, hk, rfl⟩
    rw [mul_assoc, hfR r hr, hfK k hk]
  have key : ∀ h, f h = ∑ q ∈ u, f q * (if h ∈ dcos R K q then 1 else 0) := by
    intro h
    by_cases hex : ∃ q0 ∈ u, h ∈ dcos R K q0
    · obtain ⟨q0, hq0, hh⟩ := hex
      rw [Finset.sum_eq_single q0 (fun q hq hne => ?_) (fun h' => absurd hq0 h'), if_pos hh, mul_one, hinv q0 h hh]
      rw [if_neg, mul_zero]
      intro hq'
      exact hne (hinj hq hq0 ((dcos_eq_of_mem hq').symm.trans (dcos_eq_of_mem hh)))
    · rw [Finset.sum_eq_zero fun q hq => by rw [if_neg fun hh => hex ⟨q, hq, hh⟩, mul_zero]]
      by_contra hne
      obtain ⟨q, hq, r, hr, k, hk, hh⟩ := hsupp h hne
      have hm : dcos R K q ∈ u.image (dcos R K) := himg ▸ Finset.mem_image_of_mem _ hq
      obtain ⟨q', hq', he⟩ := Finset.mem_image.1 hm
      exact hex ⟨q', hq', by rw [he]; exact ⟨r, hr, k, hk, hh⟩⟩
  have hS := quotient_integral_finset_sum u (fun q h => f q * if h ∈ dcos R K q then 1 else 0)
    (fun q => (((μ (K : Set G)).toReal / (ρ (cellSet R K q q)).toReal : ℝ) : ℂ) * f q) fun q _ => by
      have := (isQuotientIntegral_indicator_doubleCoset R K hR hKc hKo ρ μ q).smul (f q)
      convert this using 1
      · ring
  convert hS using 1
  exact funext key
end
end

section

open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CommProd

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def mulEquiv (A B : Subgroup G) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (e : (A × B) ≃ₜ G)
    (he : ∀ p, e p = p.1 * p.2) : (B × A) ≃ₜ* G where
  toFun p := (p.1 : G) * p.2
  invFun g := ((e.symm g).2, (e.symm g).1)
  left_inv p := by
    have : e.symm ((p.1 : G) * p.2) = (p.2, p.1) := by
      rw [Homeomorph.symm_apply_eq, he, hc _ p.2.2 _ p.1.2]
    simp [this]
  right_inv g := by
    change ((e.symm g).2 : G) * (e.symm g).1 = g
    rw [← hc _ (e.symm g).1.2 _ (e.symm g).2.2, ← he, e.apply_symm_apply]
  map_mul' p q := by
    change ((p.1 * q.1 : B) : G) * ((p.2 * q.2 : A) : G) = ((p.1 : G) * p.2) * ((q.1 : G) * q.2)
    simp only [Subgroup.coe_mul, mul_assoc]
    rw [← mul_assoc (p.2 : G), hc _ p.2.2 _ q.1.2]
    simp only [mul_assoc]
  continuous_toFun := (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := (e.symm.continuous.snd).prodMk (e.symm.continuous.fst)

@[simp] theorem mulEquiv_apply (A B : Subgroup G) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (e : (A × B) ≃ₜ G)
    (he : ∀ p, e p = p.1 * p.2) (p : B × A) : mulEquiv A B hc e he p = (p.1 : G) * p.2 := rfl

def mulEquivSub (A B R : Subgroup G) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (e : (A × B) ≃ₜ G)
    (he : ∀ p, e p = p.1 * p.2) (hR : ∀ a ∈ A, ∀ b ∈ B, a * b ∈ R → a ∈ R ∧ b ∈ R) :
    (R.subgroupOf B × R.subgroupOf A) ≃ₜ* R where
  toFun p := ⟨((p.1 : B) : G) * ((p.2 : A) : G), R.mul_mem (Subgroup.mem_subgroupOf.1 p.1.2) (Subgroup.mem_subgroupOf.1 p.2.2)⟩
  invFun r :=
    have h := hR _ (e.symm r).1.2 _ (e.symm r).2.2 (by rw [← he, e.apply_symm_apply]; exact r.2)
    (⟨(e.symm r).2, Subgroup.mem_subgroupOf.2 h.2⟩, ⟨(e.symm r).1, Subgroup.mem_subgroupOf.2 h.1⟩)
  left_inv p := by
    have : e.symm (((p.1 : B) : G) * ((p.2 : A) : G)) = ((p.2 : A), (p.1 : B)) := by
      rw [Homeomorph.symm_apply_eq, he, hc _ (p.2 : A).2 _ (p.1 : B).2]
    ext <;> simp [this]
  right_inv r := by
    apply Subtype.ext
    change ((e.symm r).2 : G) * (e.symm r).1 = r
    rw [← hc _ (e.symm r).1.2 _ (e.symm r).2.2, ← he, e.apply_symm_apply]
  map_mul' p q := by
    apply Subtype.ext
    change (((p.1 * q.1 : R.subgroupOf B) : B) : G) * (((p.2 * q.2 : R.subgroupOf A) : A) : G) =
      (((p.1 : B) : G) * ((p.2 : A) : G)) * (((q.1 : B) : G) * ((q.2 : A) : G))
    simp only [Subgroup.coe_mul, mul_assoc]
    rw [← mul_assoc ((p.2 : A) : G), hc _ (p.2 : A).2 _ (q.1 : B).2]
    simp only [mul_assoc]
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
  continuous_invFun := by
    have hs : Continuous fun r : R => e.symm r := e.symm.continuous.comp continuous_subtype_val
    exact ((hs.snd).subtype_mk _).prodMk ((hs.fst).subtype_mk _)

@[simp] theorem mulEquivSub_apply (A B R : Subgroup G) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (e : (A × B) ≃ₜ G)
    (he : ∀ p, e p = p.1 * p.2) (hR : ∀ a ∈ A, ∀ b ∈ B, a * b ∈ R → a ∈ R ∧ b ∈ R) (p : R.subgroupOf B × R.subgroupOf A) :
    (mulEquivSub A B R hc e he hR p : G) = ((p.1 : B) : G) * ((p.2 : A) : G) := rfl

end GlobalTheory.CommProd

namespace GlobalTheory.CommProd

theorem invInv : ∀ {X Y H : Type} [Group X] [Group Y] [Group H] [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace H] [IsTopologicalGroup X] [IsTopologicalGroup Y] [IsTopologicalGroup H] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace H] [BorelSpace X] [BorelSpace Y] [BorelSpace H] [LocallyCompactSpace X]
    [LocallyCompactSpace Y] [LocallyCompactSpace H] [SecondCountableTopology X] [SecondCountableTopology Y]
    [SecondCountableTopology H] (e : (Y × X) ≃ₜ* H) (ρ : Measure Y) (ν : Measure X) (μH : Measure H),
    ρ.IsHaarMeasure → ρ.IsInvInvariant → ν.IsHaarMeasure → μH.IsInvInvariant → (ρ.prod ν).map e = μH →
    ν.IsInvInvariant := by
  intro X Y H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e ρ ν μH _ _ _ _ h
  have he : Measurable e := e.continuous.measurable
  have h1 : (ρ.prod ν.inv).map e = μH := by
    have hp : ρ.prod ν.inv = (ρ.prod ν).map (fun p => p⁻¹) := by
      rw [show (fun p : Y × X => p⁻¹) = Prod.map (·⁻¹) (·⁻¹) from rfl,
        ← Measure.map_prod_map _ _ measurable_inv measurable_inv]
      change ρ.prod ν.inv = ρ.inv.prod ν.inv
      rw [Measure.inv_eq_self ρ]
    have hc : (e ∘ fun p : Y × X => p⁻¹) = (fun q : H => q⁻¹) ∘ e := funext fun p => map_inv e p
    rw [hp, Measure.map_map he measurable_inv, hc, ← Measure.map_map measurable_inv he, h]
    exact Measure.inv_eq_self μH
  have h2 : ρ.prod ν.inv = ρ.prod ν := by
    let E := e.toHomeomorph.toMeasurableEquiv
    have hE : (E : Y × X → H) = e := rfl
    rw [← E.map_symm_map (μ := ρ.prod ν.inv), ← E.map_symm_map (μ := ρ.prod ν), hE, h1, h]
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : Y)
  have hK0 : ρ K ≠ 0 := (Measure.measure_pos_of_mem_nhds (μ := ρ) hK1).ne'
  have hKt : ρ K ≠ ⊤ := hK.measure_lt_top.ne
  refine ⟨Measure.ext fun S hS => ?_⟩
  have := congrArg (fun m : Measure (Y × X) => m (K ×ˢ S)) h2
  simp only [Measure.prod_prod] at this
  exact (ENNReal.mul_right_inj hK0 hKt).1 this

theorem cutProd : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (A B R : Subgroup G)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (e : (A × B) ≃ₜ G) (he : ∀ p, e p = p.1 * p.2)
    (hR : ∀ a ∈ A, ∀ b ∈ B, a * b ∈ R → a ∈ R ∧ b ∈ R) (μR : Measure R) (ρ : Measure (R.subgroupOf B))
    (ν : Measure (R.subgroupOf A)) (βB : B → NNReal) (βA : A → NNReal), SFinite ρ → SFinite ν →
    (ρ.prod ν).map (mulEquivSub A B R hc e he hR) = μR →
    GlobalTheory.Tw.IsCosetCutoff (R.subgroupOf B) ρ βB → GlobalTheory.Tw.IsCosetCutoff (R.subgroupOf A) ν βA →
    GlobalTheory.Tw.IsCosetCutoff R μR (fun g => βB (e.symm g).2 * βA (e.symm g).1) := by
  intro G _ _ _ _ _ _ _ _ A B R hc e he hR μR ρ ν βB βA _ _ hm hB hA
  have hs : Measurable fun g : G => e.symm g := e.symm.continuous.measurable
  have hmeas : Measurable fun g : G => βB (e.symm g).2 * βA (e.symm g).1 :=
    (hB.1.comp (measurable_snd.comp hs)).mul (hA.1.comp (measurable_fst.comp hs))
  refine ⟨hmeas, fun x => ?_⟩
  set ψ := mulEquivSub A B R hc e he hR
  have hψ : Measurable ψ := ψ.continuous.measurable
  have hmx : Measurable fun r : R => ((βB (e.symm ((r : G) * x)).2 * βA (e.symm ((r : G) * x)).1 : NNReal) : ℝ≥0∞) :=
    (hmeas.comp (measurable_subtype_coe.mul_const x)).coe_nnreal_ennreal
  rw [← hm, lintegral_map hmx hψ]
  have key : ∀ p : R.subgroupOf B × R.subgroupOf A, e.symm ((ψ p : G) * x) = ((p.2 : A) * (e.symm x).1, (p.1 : B) * (e.symm x).2) := by
    intro p
    rw [Homeomorph.symm_apply_eq, he, mulEquivSub_apply]
    have hx : x = ((e.symm x).1 : G) * (e.symm x).2 := by rw [← he, e.apply_symm_apply]
    have h1 : ((p.1 : B) : G) * ((p.2 : A) : G) = ((p.2 : A) : G) * ((p.1 : B) : G) :=
      (hc _ (p.2 : A).2 _ (p.1 : B).2).symm
    have h2 : ((p.1 : B) : G) * ((e.symm x).1 : G) = ((e.symm x).1 : G) * ((p.1 : B) : G) :=
      (hc _ (e.symm x).1.2 _ (p.1 : B).2).symm
    calc ((p.1 : B) : G) * ((p.2 : A) : G) * x
        = ((p.2 : A) : G) * (((p.1 : B) : G) * ((e.symm x).1 : G)) * (e.symm x).2 := by
          rw [h1]; conv_lhs => rw [hx]
          simp only [mul_assoc]
      _ = _ := by rw [h2]; simp only [Subgroup.coe_mul, mul_assoc]
  simp only [key, ENNReal.coe_mul]
  refine (lintegral_prod _ ((hB.1.coe_nnreal_ennreal.comp ((measurable_subtype_coe.comp measurable_fst).mul_const _)).mul
    (hA.1.coe_nnreal_ennreal.comp ((measurable_subtype_coe.comp measurable_snd).mul_const _))).aemeasurable).trans ?_
  simp only [Pi.mul_apply, Function.comp_apply, lintegral_const_mul' _ _ ENNReal.coe_ne_top, hA.2, mul_one, hB.2]

end GlobalTheory.CommProd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.CommProd in
theorem GlobalTheory.CommProd.quot_vanish_of_prod : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (A B R : Subgroup G), IsClosed (A : Set G) → IsClosed (B : Set G) → IsClosed (R : Set G) → (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) → (∃ e : (A × B) ≃ₜ G, ∀ p, e p = p.1 * p.2) → (∀ a ∈ A, ∀ b ∈ B, a * b ∈ R → a ∈ R ∧ b ∈ R) → ∀ (μR : Measure R) (μG : Measure G) (ρ : Measure (R.subgroupOf B)) (μ : Measure B), μR.IsHaarMeasure → μR.IsInvInvariant → μG.IsHaarMeasure → ρ.IsHaarMeasure → ρ.IsInvInvariant → μ.IsHaarMeasure → ∀ (f : G → ℂ) (z : ℂ), IsQuotIntL1 μR μG f z → (∀ a ∈ A, IsQuotIntL1 ρ μ (fun b => f (a * b.1)) 0) → z = 0 := by
  intro G _ _ _ _ _ _ _ _ A B R hA hB hR hc ⟨e, he⟩ hdec μR μG ρ μ _ _ _ _ _ _ f z hf hz
  have : LocallyCompactSpace A := hA.locallyCompactSpace
  have : LocallyCompactSpace B := hB.locallyCompactSpace
  have hRA : IsClosed ((R.subgroupOf A : Subgroup A) : Set A) := hR.preimage continuous_subtype_val
  have hRB : IsClosed ((R.subgroupOf B : Subgroup B) : Set B) := hR.preimage continuous_subtype_val
  have : LocallyCompactSpace (R.subgroupOf A) := hRA.locallyCompactSpace
  have : LocallyCompactSpace (R.subgroupOf B) := hRB.locallyCompactSpace
  have : LocallyCompactSpace R := hR.locallyCompactSpace
  let φ := mulEquiv A B hc e he
  let ψ := mulEquivSub A B R hc e he hdec
  obtain ⟨μA, hμA, hG⟩ := GlobalTheory.St.HaarSplit.exists_haar_map_prod_eq φ μ μG
  obtain ⟨ν, hν, hRm⟩ := GlobalTheory.St.HaarSplit.exists_haar_map_prod_eq ψ ρ μR
  have : ν.IsInvInvariant := invInv ψ ρ ν μR inferInstance inferInstance hν inferInstance hRm
  obtain ⟨βB, -, hβB⟩ := GlobalTheory.Tw.exists_isCosetCutoff (μT := ρ) hRB
  obtain ⟨βA, -, hβA⟩ := GlobalTheory.Tw.exists_isCosetCutoff (μT := ν) hRA
  have hβ := cutProd G A B R hc e he hdec μR ρ ν βB βA inferInstance inferInstance hRm hβB hβA
  obtain ⟨hi, rfl⟩ := hf.cutoff hβ
  have hφs : ∀ p : B × A, e.symm (φ p) = (p.2, p.1) := fun p => by
    rw [Homeomorph.symm_apply_eq, he, mulEquiv_apply, hc _ p.2.2 _ p.1.2]
  have hme : MeasurableEmbedding φ := φ.toHomeomorph.measurableEmbedding
  rw [← hG] at hi ⊢
  rw [hme.integral_map]
  rw [hme.integrable_map_iff] at hi
  refine (integral_prod_symm _ hi).trans ?_
  have hin : ∀ a : A, ∫ b : B, ((fun g => ((βB (e.symm g).2 * βA (e.symm g).1 : NNReal) : ℝ) • f g) ∘ φ) (b, a) ∂μ = 0 := by
    intro a
    obtain ⟨-, h0⟩ := (hz a a.2).cutoff hβB
    have e1 : ∀ b : B, ((fun g => ((βB (e.symm g).2 * βA (e.symm g).1 : NNReal) : ℝ) • f g) ∘ φ) (b, a) =
        (βA a : ℝ) • ((βB b : ℝ) • f (a * b)) := fun b => by
      simp only [Function.comp_apply, hφs, mulEquiv_apply, NNReal.coe_mul, smul_smul]
      rw [show φ (b, a) = (b : G) * a from rfl, hc _ a.2 _ b.2, mul_comm (βB b : ℝ)]
    simp only [e1, integral_smul, ← h0, smul_zero]
  exact (integral_congr_ae (Filter.Eventually.of_forall hin)).trans (integral_zero _ _)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

noncomputable section




namespace GlobalTheory.IwaPlace.GramBasis

variable {D : D7} {S : HSp D}

def cv {n : ℕ} (y : Fin n → AE D) : Fin n → AE D := fun i => cA D (y i)

theorem hermAt_eq (x y : Fin S.rank → AE D) : hermAt S x y = cv y ⬝ᵥ (gA S *ᵥ x) := by
  unfold hermAt cv
  simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem cv_mulVec {m : ℕ} (N : Matrix (Fin S.rank) (Fin m) (AE D)) (b : Fin m → AE D) :
    cv (N *ᵥ b) = vecMul (cv b) (adj N) := by
  funext i

  simp only [cv, mulVec, vecMul, dotProduct, map_sum, map_mul, adj, transpose_apply, map_apply]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem hermAt_mulVec {m n : ℕ} (M : Matrix (Fin S.rank) (Fin m) (AE D)) (a : Fin m → AE D)
    (N : Matrix (Fin S.rank) (Fin n) (AE D)) (b : Fin n → AE D) :
    hermAt S (M *ᵥ a) (N *ᵥ b) = cv b ⬝ᵥ ((adj N * (gA S * M)) *ᵥ a) := by
  rw [hermAt_eq, cv_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

theorem cv_single {n : ℕ} (i : Fin n) : cv (Pi.single i (1 : AE D)) = Pi.single i 1 := by
  funext k
  by_cases h : k = i
  · subst h; simp [cv]
  · simp [cv, Pi.single_eq_of_ne h]

theorem mulVec_single_apply {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) (i : Fin m) (j : Fin n) :
    (M *ᵥ Pi.single j (1 : AE D)) i = M i j := by
  rw [mulVec_single_one]; rfl

theorem gram_basis : ∀ (D : D7) (S : HSp D) (v : Pl D) (ε : AE D) (Λ : AddSubgroup (Fin S.rank → AE D)) (β β' : Matrix (Fin S.rank) (Fin S.rank) (AE D)), ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → IsSDAt S v Λ → (∀ i j, β i j ∈ idAt D (· = v)) → (∀ i j, β' i j ∈ idAt D (· = v)) → β * β' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) → β' * β = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) → (∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ ∀ i, (β' *ᵥ y) i ∈ intAt D (· = v))) → (∀ i j, (adj β * (gA S * β)) i j ∈ intAt D (· = v)) ∧ (∀ i j, cA D ((adj β * (gA S * β)) i j) = (adj β * (gA S * β)) j i) ∧ ∃ H' : Matrix (Fin S.rank) (Fin S.rank) (AE D), (∀ i j, H' i j ∈ intAt D (· = v)) ∧ adj β * (gA S * β) * H' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
  intro D S v ε Λ β β' hεε hcε hε hact hΛ hβ hβ' h1 h2 hmem
  have h0 : (0 : AE D) ∈ intAt D (· = v) := ⟨zero_mem _, by rw [RingHom.map_zero]; exact zero_mem _⟩
  have hcs : ∀ j k, (β *ᵥ Pi.single j (1 : AE D)) k ∈ idAt D (· = v) := fun j k => by
    rw [mulVec_single_apply]; exact hβ k j
  have hcol : ∀ j, β *ᵥ Pi.single j (1 : AE D) ∈ Λ := fun j => (hmem _ (hcs j)).2 fun i => by
    rw [mulVec_mulVec, mulVec_single_apply, h2, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    split_ifs
    · rw [mul_one]; exact hε
    · rw [mul_zero]; exact h0
  have hadj : adj β * adj β' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
    rw [← adj_mul, h2, adj_smul, adj_one, hcε]
  have hz : adj β * (gA S * (giA S * adj β')) = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
    rw [gA_giA_cancel, hadj]
  refine ⟨fun i j => ?_, fun i j => ?_, β' * (giA S * adj β'), fun i j => ?_, ?_⟩
  · have h := (hΛ.2.2 _ (hcs j)).1 (hcol j) _ (hcol i)
    rwa [hermAt_mulVec, cv_single, single_dotProduct, one_mul, mulVec_single_apply] at h
  · have h : adj (adj β * (gA S * β)) = adj β * (gA S * β) := by
      rw [adj_mul, adj_mul, adj_gA, adj_adj, Matrix.mul_assoc]
    exact congrFun (congrFun h j) i
  · have hs : ∀ k, ((giA S * adj β') *ᵥ Pi.single j (1 : AE D)) k ∈ idAt D (· = v) := fun k => by
      rw [← mulVec_mulVec]
      refine mulVec_mem_idAt _ (fun l => ?_) k
      rw [mulVec_single_apply]
      change cA D (β' j l) ∈ _
      rw [← (hact _).1 (hβ' j l), RingHom.map_mul, hcε]
      exact Ideal.mul_mem_right _ _ hε.1
    have hin : (giA S * adj β') *ᵥ Pi.single j (1 : AE D) ∈ Λ := (hΛ.2.2 _ hs).2 fun x hx => by
      refine ⟨LocSD.hermAt_mem_idAt hs x, ?_⟩
      have hw := (hmem x (hΛ.1 x hx)).1 hx j
      have e : x = β *ᵥ (β' *ᵥ x) := by
        rw [mulVec_mulVec, h1, smul_mulVec, one_mulVec]
        funext k
        exact ((hact _).1 (hΛ.1 x hx k)).symm
      rw [e, hermAt_mulVec, hz, smul_mulVec, one_mulVec, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul,
        RingHom.map_mul]
      exact FrameLat.mul_mem_intAE hε.2 ((FrameLat.cA_int_iff _).2 hw.2)
    have h := (hmem _ hs).1 hin i
    rwa [mulVec_mulVec, mulVec_single_apply] at h
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc β, h1, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_smul, hz, smul_smul, hεε]

end GlobalTheory.IwaPlace.GramBasis

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unramified_hecke_vacuum_larger_eq_smaller : GlobalTheory.Hk3.HoweUnram → ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∀ h' ∈ Hecke ℂ (KU σ n'), ∃ h ∈ Hecke ℂ (KU σ n), heckeVec (ω.comp (MonoidHom.inl _ _)) (KU σ n) h s = heckeVec (ω.comp (MonoidHom.inr _ _)) (KU σ n') h' s := by
  first | exact @GlobalTheory.ChainOnto.heckeVec_howe | exact GlobalTheory.ChainOnto.heckeVec_howe | (intros; apply GlobalTheory.ChainOnto.heckeVec_howe <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integral_heisenberg_invariant_forms_proportional : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∀ l e : M →ₗ[ℂ] ℂ, (∀ u ∈ intMat L (Fin n') (Fin n), ∀ m, l (ρ u m) = l m) → (∀ u ∈ intMat L (Fin n') (Fin n), ∀ m, e (ρ u m) = e m) → ∀ m, e m * l s = l m * e s := by
  first | exact @GlobalTheory.ChainOnto.heisInv_forms_proportional | exact GlobalTheory.ChainOnto.heisInv_forms_proportional | (intros; apply GlobalTheory.ChainOnto.heisInv_forms_proportional <;> assumption)
end
