module

public import Mathlib.GroupTheory.Index
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure

@[expose] public section

section

noncomputable section

namespace PI.IwaMeasEx.MF

open MeasureTheory Measure Set
open scoped ENNReal NNReal

section Idx

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

theorem measure_eq_relIndex_mul (μ : Measure G) [IsMulLeftInvariant μ] {U W : Subgroup G} (hWU : W ≤ U)
    (hU : MeasurableSet (U : Set G)) (hW : MeasurableSet (W : Set G)) (hfin : W.relIndex U ≠ 0) :
    μ U = W.relIndex U * μ W := by
  classical
  have hcard : Nat.card (U ⧸ W.subgroupOf U) = W.relIndex U := rfl
  haveI : Finite (U ⧸ W.subgroupOf U) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hfin)
  letI : Fintype (U ⧸ W.subgroupOf U) := Fintype.ofFinite _
  choose r hr using fun q : U ⧸ W.subgroupOf U => QuotientGroup.mk_surjective q
  have hC : (U : Set G) = ⋃ q, (fun x => ((r q : U) : G)⁻¹ * x) ⁻¹' (W : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · intro hx
      refine ⟨(QuotientGroup.mk (⟨x, hx⟩ : U) : U ⧸ W.subgroupOf U), ?_⟩
      have h := QuotientGroup.eq.mp (hr (QuotientGroup.mk (⟨x, hx⟩ : U)))
      rw [Subgroup.mem_subgroupOf] at h
      simpa using h
    · rintro ⟨q, hq⟩
      have e : x = ((r q : U) : G) * (((r q : U) : G)⁻¹ * x) := by group
      rw [e]
      exact U.mul_mem (r q).2 (hWU hq)
  have hdisj : Pairwise (Function.onFun Disjoint fun q => (fun x => ((r q : U) : G)⁻¹ * x) ⁻¹' (W : Set G)) := by
    intro q q' hne
    change Disjoint ((fun x => ((r q : U) : G)⁻¹ * x) ⁻¹' (W : Set G))
      ((fun x => ((r q' : U) : G)⁻¹ * x) ⁻¹' (W : Set G))
    refine Set.disjoint_left.mpr ?_
    intro x hx hx'
    apply hne
    simp only [Set.mem_preimage, SetLike.mem_coe] at hx hx'
    rw [← hr q, ← hr q']
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.mem_subgroupOf]
    have key : ((r q : U) : G)⁻¹ * ((r q' : U) : G) ∈ W := by
      have e : ((r q : U) : G)⁻¹ * ((r q' : U) : G) =
          (((r q : U) : G)⁻¹ * x) * (((r q' : U) : G)⁻¹ * x)⁻¹ := by group
      rw [e]
      exact W.mul_mem hx (W.inv_mem hx')
    simpa using key
  have hmeas : ∀ q, MeasurableSet ((fun x => ((r q : U) : G)⁻¹ * x) ⁻¹' (W : Set G)) :=
    fun q => hW.preimage (measurable_const_mul _)
  have hval : ∀ q, μ ((fun x => ((r q : U) : G)⁻¹ * x) ⁻¹' (W : Set G)) = μ W :=
    fun q => measure_preimage_mul μ _ _
  have hfc : (Fintype.card (U ⧸ W.subgroupOf U) : ℝ≥0∞) = (W.relIndex U : ℝ≥0∞) := by
    rw [← Nat.card_eq_fintype_card, hcard]
  rw [hC, measure_iUnion hdisj hmeas, tsum_fintype]
  simp only [hval, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hfc]

end Idx

section Conj

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

end Conj

section Scale

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G]

end Scale

end PI.IwaMeasEx.MF

end
end

section

noncomputable section

namespace PI.IwaMeasEx.MH

open MeasureTheory Measure Topology Set Filter
open scoped ENNReal NNReal

section Gen

variable {A : Type*} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
  [T2Space A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]

theorem nnreal_eq_of_smul (μ : Measure A) [μ.IsAddHaarMeasure] {a b : ℝ≥0} (h : a • μ = b • μ) : a = b := by
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts A) := inferInstance
  have h0 : μ K ≠ 0 := (measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
  have ht : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have hK := congrArg (fun ν : Measure A => ν K) h
  simp only [Measure.smul_apply, nnreal_smul_coe_apply] at hK
  exact_mod_cast (ENNReal.mul_left_inj h0 ht).1 hK

theorem char_eq_of_map (μ : Measure A) [μ.IsAddHaarMeasure] [μ.Regular] (φ : A ≃ₜ+ A) {c : ℝ≥0} (hc : c ≠ 0)
    (h : μ.map φ = c • μ) : addEquivAddHaarChar φ = c⁻¹ := by
  have h1 := addEquivAddHaarChar_smul_map μ φ
  rw [h, smul_smul] at h1
  exact eq_inv_of_mul_eq_one_left (nnreal_eq_of_smul μ (h1.trans (one_smul _ _).symm))

theorem map_char (μ : Measure A) [μ.IsAddHaarMeasure] [μ.Regular] (φ : A ≃ₜ+ A) :
    μ.map φ = (addEquivAddHaarChar φ)⁻¹ • μ := by
  conv_rhs => rw [← addEquivAddHaarChar_smul_map μ φ]
  rw [smul_smul, inv_mul_cancel₀ (addEquivAddHaarChar_pos φ).ne', one_smul]

variable {B : Type*} [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] [LocallyCompactSpace B]
  [T2Space B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]

theorem char_transport (e : A ≃ₜ+ B) (φ : A ≃ₜ+ A) :
    addEquivAddHaarChar ((e.symm.trans φ).trans e) = addEquivAddHaarChar φ := by
  have : ((addHaar : Measure A).map e).IsAddHaarMeasure := e.isAddHaarMeasure_map _
  have : ((addHaar : Measure A).map e).Regular := Regular.map e.toHomeomorph
  refine (char_eq_of_map ((addHaar : Measure A).map e) _
    (inv_ne_zero (addEquivAddHaarChar_pos φ).ne') ?_).trans (inv_inv _)
  have hcomp : ((e.symm.trans φ).trans e : B → B) ∘ e = e ∘ φ := by
    funext x
    simp
  rw [Measure.map_map (map_continuous _).measurable (map_continuous e).measurable, hcomp,
    ← Measure.map_map (map_continuous e).measurable (map_continuous φ).measurable,
    map_char (addHaar : Measure A) φ, Measure.map_smul]
  exact e.continuous.measurable.aemeasurable

def prodE (φ : A ≃ₜ+ A) (ψ : B ≃ₜ+ B) : A × B ≃ₜ+ A × B where
  toFun p := (φ p.1, ψ p.2)
  invFun p := (φ.symm p.1, ψ.symm p.2)
  left_inv p := by simp
  right_inv p := by simp
  map_add' p q := by simp
  continuous_toFun := (φ.continuous.comp continuous_fst).prodMk (ψ.continuous.comp continuous_snd)
  continuous_invFun := (φ.symm.continuous.comp continuous_fst).prodMk (ψ.symm.continuous.comp continuous_snd)

theorem char_prod (φ : A ≃ₜ+ A) (ψ : B ≃ₜ+ B) :
    addEquivAddHaarChar (prodE φ ψ) = addEquivAddHaarChar φ * addEquivAddHaarChar ψ := by
  have hmap : ((addHaar : Measure A).prod (addHaar : Measure B)).map (prodE φ ψ) =
      ((addEquivAddHaarChar φ)⁻¹ * (addEquivAddHaarChar ψ)⁻¹) •
        ((addHaar : Measure A).prod (addHaar : Measure B)) := by
    rw [show (prodE φ ψ : A × B → A × B) = Prod.map φ ψ from rfl,
      ← Measure.map_prod_map _ _ (map_continuous φ).measurable (map_continuous ψ).measurable,
      map_char (addHaar : Measure A) φ, map_char (addHaar : Measure B) ψ,
      Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  rw [char_eq_of_map _ _ (mul_ne_zero (inv_ne_zero (addEquivAddHaarChar_pos φ).ne')
    (inv_ne_zero (addEquivAddHaarChar_pos ψ).ne')) hmap, mul_inv, inv_inv, inv_inv]

end Gen

end PI.IwaMeasEx.MH

end
end

section

noncomputable section

namespace PI.IwaMeasEx.MG

open MeasureTheory Measure Topology Set
open scoped ENNReal NNReal

theorem smul_cancel {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [LocallyCompactSpace Y]
    (ρ : Measure Y) [IsFiniteMeasureOnCompacts ρ] [ρ.IsOpenPosMeasure] [Nonempty Y] {a b : ℝ≥0}
    (h : a • ρ = b • ρ) : a = b := by
  obtain ⟨x⟩ := ‹Nonempty Y›
  obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x
  have h0 : ρ K ≠ 0 := (measure_pos_of_mem_nhds ρ hKx).ne'
  have htop : ρ K ≠ ∞ := hK.measure_lt_top.ne
  have hK' : (a : ℝ≥0∞) * ρ K = (b : ℝ≥0∞) * ρ K := by
    have e := congrArg (fun m : Measure Y => m K) h
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e
    exact e
  have hab : (a : ℝ≥0∞) = b := (ENNReal.mul_left_inj h0 htop).mp hK'
  exact_mod_cast hab

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]
variable {Y : Type*} [AddCommGroup Y] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [IsTopologicalAddGroup Y] [LocallyCompactSpace Y]

theorem mulEquivHaarChar_eq_of_chart (μ : Measure G) [IsHaarMeasure μ] [Regular μ] (ν : Measure Y)
    [IsAddHaarMeasure ν] [Regular ν] (χ : G → Y) (hχm : Measurable χ) (hχ : μ.map χ = ν) (φ : G ≃ₜ* G)
    (L : Y ≃ₜ+ Y) (h : ∀ x, χ (φ x) = L (χ x)) : mulEquivHaarChar φ = addEquivAddHaarChar L := by
  have hφ : Measurable φ := (map_continuous φ).measurable
  have hL : Measurable L := (map_continuous L).measurable
  have hcomp : χ ∘ φ = L ∘ χ := funext h
  have h1 : mulEquivHaarChar φ • map L ν = ν := by
    have e := congrArg (Measure.map χ) (mulEquivHaarChar_smul_map μ φ)
    rw [Measure.map_smul, Measure.map_map hχm hφ, hcomp, ← Measure.map_map hL hχm, hχ] at e
      <;> try exact hχm.aemeasurable
    exact e
  have h2 : addEquivAddHaarChar L • map L ν = ν := addEquivAddHaarChar_smul_map ν L
  have h3 : addEquivAddHaarChar L • ν = mulEquivHaarChar φ • ν := by
    calc addEquivAddHaarChar L • ν = addEquivAddHaarChar L • (mulEquivHaarChar φ • map L ν) := by rw [h1]
      _ = mulEquivHaarChar φ • (addEquivAddHaarChar L • map L ν) := by
        rw [smul_smul, smul_smul, mul_comm]
      _ = mulEquivHaarChar φ • ν := by rw [h2]
  exact (smul_cancel ν h3).symm

theorem shear_map {A B : Type*} [MeasurableSpace A] [AddGroup B] [MeasurableSpace B] [MeasurableAdd₂ B]
    [MeasurableAdd B] (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν] [ν.IsAddRightInvariant]
    (f : A → B) (hf : Measurable f) :
    (μ.prod ν).map (fun p : A × B => (p.1, p.2 + f p.1)) = μ.prod ν := by
  have hm : Measurable (fun p : A × B => (p.1, p.2 + f p.1)) :=
    measurable_fst.prodMk (measurable_snd.add (hf.comp measurable_fst))
  ext s hs
  rw [Measure.map_apply hm hs, Measure.prod_apply hs, Measure.prod_apply (hm hs)]
  refine lintegral_congr fun x => ?_
  have hpre : Prod.mk x ⁻¹' ((fun p : A × B => (p.1, p.2 + f p.1)) ⁻¹' s)
      = (fun b => b + f x) ⁻¹' (Prod.mk x ⁻¹' s) := rfl
  rw [hpre, measure_preimage_add_right]

end PI.IwaMeasEx.MG

end
end
