module

public import GroundTheory.LocalFields.Bundle004
public import GroundTheory.LocalFields.UnitsPowers
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import GroundTheory.LocalFields.Interface
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import GroundTheory.LocalFields.Eisenstein
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

@[expose] public section

section

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

section Inertia

theorem integerAlgEquiv_teichmuller {σ : L ≃ₐ[K] L} (hσ : σ ∈ lowerRamificationGroup K L 0)
    (ζ : 𝓀[L]ˣ) :
    integerAlgEquiv K L σ (teichmuller L ζ : 𝒪[L]) = teichmuller L ζ := by
  have hres : unitsToResidue L (Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L])
      (teichmuller L ζ)) = unitsToResidue L (teichmuller L ζ) := by
    ext
    exact residue_integerAlgEquiv_of_mem_zero K L hσ _
  have hpow : Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L]) (teichmuller L ζ) ^
      (Nat.card 𝓀[L] - 1) = 1 := by
    rw [← map_pow, teichmuller_pow_card_sub_one, map_one]
  exact congrArg Units.val (eq_of_pow_card_sub_one hpow (teichmuller_pow_card_sub_one ζ) hres)

theorem sub_mem_of_uniformizer {σ : L ≃ₐ[K] L} (hσ : σ ∈ lowerRamificationGroup K L 0)
    {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) {n : ℕ}
    (h : integerAlgEquiv K L σ ϖ - ϖ ∈ 𝓂[L] ^ n) (x : 𝒪[L]) :
    integerAlgEquiv K L σ x - x ∈ 𝓂[L] ^ n := by
  set e := integerAlgEquiv K L σ
  let P : 𝒪[L] → Prop := fun y ↦ e y - y ∈ 𝓂[L] ^ n
  have hadd : ∀ a b, P a → P b → P (a + b) := fun a b ha hb ↦ by
    have : e (a + b) - (a + b) = (e a - a) + (e b - b) := by rw [map_add (f := _)]; ring
    simp only [P, this]
    exact add_mem ha hb
  have hmul : ∀ a b, P a → P b → P (a * b) := fun a b ha hb ↦ by
    have : e (a * b) - a * b = e a * (e b - b) + (e a - a) * b := by rw [map_mul]; ring
    simp only [P, this]
    exact add_mem (Ideal.mul_mem_left _ _ hb) (Ideal.mul_mem_right _ _ ha)
  have hpow : ∀ a (k : ℕ), P a → P (a ^ k) := by
    intro a k ha
    induction k with
    | zero => simp [P]
    | succ k ih => rw [pow_succ]; exact hmul _ _ ih ha
  have hfix : ∀ a, e a = a → P a := fun a ha ↦ by simp [P, ha]
  have hideal : ∀ y ∈ 𝓂[L] ^ n, P y := fun y hy ↦
    sub_mem ((integerAlgEquiv_mem_maximalIdeal_pow_iff σ n y).mpr hy) hy
  have happrox : ∀ y : 𝒪[L], ∃ t, e t = t ∧ y - t ∈ 𝓂[L] := by
    intro y
    by_cases hy : residue 𝒪[L] y = 0
    · exact ⟨0, map_zero e, by simpa using (residue_eq_zero_iff y).mp hy⟩
    · refine ⟨teichmuller L (Units.mk0 _ hy), integerAlgEquiv_teichmuller hσ _, ?_⟩
      rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
      exact (congrArg Units.val (unitsToResidue_teichmuller (K := L) (Units.mk0 _ hy))).symm
  have hstep : ∀ m : ℕ, ∃ r, P r ∧ x - r ∈ 𝓂[L] ^ m := by
    intro m
    induction m with
    | zero => exact ⟨0, by simp [P], by simp⟩
    | succ m ih =>
      obtain ⟨r, hr, hxr⟩ := ih
      obtain ⟨y, hy⟩ := (mem_maximalIdeal_pow_iff hϖ).mp hxr
      obtain ⟨t, ht, hyt⟩ := happrox y
      obtain ⟨z, hz⟩ := (mem_maximalIdeal_iff_dvd hϖ).mp hyt
      refine ⟨r + ϖ ^ m * t, hadd _ _ hr (hmul _ _ (hpow _ _ h) (hfix _ ht)), ?_⟩
      rw [mem_maximalIdeal_pow_iff hϖ]
      exact ⟨z, by rw [pow_succ]; linear_combination hy + ϖ ^ m * hz⟩
  obtain ⟨r, hr, hxr⟩ := hstep n
  have : x = r + (x - r) := by ring
  rw [this]
  exact hadd _ _ hr (hideal _ hxr)

theorem mem_lowerRamificationGroup_iff_uniformizer {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ lowerRamificationGroup K L 0) {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) (n : ℕ) :
    σ ∈ lowerRamificationGroup K L n ↔ integerAlgEquiv K L σ ϖ - ϖ ∈ 𝓂[L] ^ (n + 1) :=
  ⟨fun h ↦ mem_lowerRamificationGroup_natCast_iff.mp h ϖ,
    fun h ↦ mem_lowerRamificationGroup_natCast_iff.mpr (sub_mem_of_uniformizer hσ hϖ h)⟩

end Inertia

section Ratio

theorem irreducible_integerAlgEquiv (σ : L ≃ₐ[K] L) {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) :
    Irreducible (integerAlgEquiv K L σ ϖ) :=
  (MulEquiv.irreducible_iff (f := (integerAlgEquiv K L σ : 𝒪[L] ≃* 𝒪[L]))).mpr hϖ

def uniformizerRatio {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) (σ : L ≃ₐ[K] L) : 𝒪[L]ˣ :=
  (IsDiscreteValuationRing.associated_of_irreducible 𝒪[L] hϖ
    (irreducible_integerAlgEquiv σ hϖ)).choose

variable {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
include hϖ

theorem mul_uniformizerRatio (σ : L ≃ₐ[K] L) :
    ϖ * uniformizerRatio hϖ σ = integerAlgEquiv K L σ ϖ :=
  (IsDiscreteValuationRing.associated_of_irreducible 𝒪[L] hϖ
    (irreducible_integerAlgEquiv σ hϖ)).choose_spec

theorem uniformizerRatio_eq_iff (σ : L ≃ₐ[K] L) (u : 𝒪[L]ˣ) :
    uniformizerRatio hϖ σ = u ↔ ϖ * u = integerAlgEquiv K L σ ϖ := by
  refine ⟨fun h ↦ h ▸ mul_uniformizerRatio hϖ σ, fun h ↦ Units.ext ?_⟩
  exact mul_left_cancel₀ hϖ.ne_zero ((mul_uniformizerRatio hϖ σ).trans h.symm)

@[simp]
theorem uniformizerRatio_one : uniformizerRatio hϖ (1 : L ≃ₐ[K] L) = 1 := by
  rw [uniformizerRatio_eq_iff, map_one, AlgEquiv.one_apply, Units.val_one, mul_one]

theorem uniformizerRatio_mul (σ τ : L ≃ₐ[K] L) :
    uniformizerRatio hϖ (σ * τ) = uniformizerRatio hϖ σ *
      Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L]) (uniformizerRatio hϖ τ) := by
  rw [uniformizerRatio_eq_iff, map_mul, AlgEquiv.mul_apply, ← mul_uniformizerRatio hϖ τ, map_mul,
    ← mul_uniformizerRatio hϖ σ, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, mul_assoc]

theorem mem_lowerRamificationGroup_iff_uniformizerRatio {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ lowerRamificationGroup K L 0) (n : ℕ) :
    σ ∈ lowerRamificationGroup K L n ↔ uniformizerRatio hϖ σ ∈ unitFiltration L n := by
  rw [mem_lowerRamificationGroup_iff_uniformizer hσ hϖ, mem_unitFiltration,
    ← mul_uniformizerRatio hϖ σ, mem_maximalIdeal_pow_iff hϖ, mem_maximalIdeal_pow_iff hϖ,
    show ϖ * (uniformizerRatio hϖ σ : 𝒪[L]) - ϖ = ϖ * ((uniformizerRatio hϖ σ : 𝒪[L]) - 1) by ring,
    pow_succ', mul_dvd_mul_iff_left hϖ.ne_zero]

theorem uniformizerRatio_mem {n : ℕ} (σ : lowerRamificationGroup K L n) :
    uniformizerRatio hϖ (σ : L ≃ₐ[K] L) ∈ unitFiltration L n :=
  (mem_lowerRamificationGroup_iff_uniformizerRatio hϖ
    (lowerRamificationGroup_antitone K L (by omega) σ.2) n).mp σ.2


omit hϖ in
theorem map_mul_inv_mem {n : ℕ} {σ : L ≃ₐ[K] L} (hσ : σ ∈ lowerRamificationGroup K L n)
    (u : 𝒪[L]ˣ) :
    Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L]) u * u⁻¹ ∈ unitFiltration L (n + 1) := by
  rw [mem_unitFiltration]
  have h : ((Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L]) u * u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) - 1 =
      (integerAlgEquiv K L σ u - u) * ((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) := by
    rw [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, sub_mul, Units.mul_inv]
  rw [h]
  exact Ideal.mul_mem_right _ _ (mem_lowerRamificationGroup_natCast_iff.mp hσ (u : 𝒪[L]))


omit hϖ in
abbrev unitFiltrationSucc (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] (n : ℕ) : Subgroup (unitFiltration L n) :=
  (unitFiltration L (n + 1)).subgroupOf (unitFiltration L n)

def ramificationToUnits (n : ℕ) :
    lowerRamificationGroup K L n →* unitFiltration L n ⧸ unitFiltrationSucc L n where
  toFun σ := QuotientGroup.mk ⟨uniformizerRatio hϖ (σ : L ≃ₐ[K] L), uniformizerRatio_mem hϖ σ⟩
  map_one' := by
    have : (⟨uniformizerRatio hϖ ((1 : lowerRamificationGroup K L n) : L ≃ₐ[K] L),
      uniformizerRatio_mem hϖ 1⟩ : unitFiltration L n) = 1 := Subtype.ext (uniformizerRatio_one hϖ)
    rw [this, QuotientGroup.mk_one]
  map_mul' σ τ := by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h := map_mul_inv_mem σ.2 (uniformizerRatio hϖ (τ : L ≃ₐ[K] L))
    have key : (((⟨uniformizerRatio hϖ ((σ * τ : lowerRamificationGroup K L n) : L ≃ₐ[K] L),
        uniformizerRatio_mem hϖ (σ * τ)⟩ : unitFiltration L n)⁻¹ *
        (⟨uniformizerRatio hϖ (σ : L ≃ₐ[K] L), uniformizerRatio_mem hϖ σ⟩ *
          ⟨uniformizerRatio hϖ (τ : L ≃ₐ[K] L), uniformizerRatio_mem hϖ τ⟩) : unitFiltration L n) : 𝒪[L]ˣ) =
        (Units.map (integerAlgEquiv K L (σ : L ≃ₐ[K] L) : 𝒪[L] →* 𝒪[L])
          (uniformizerRatio hϖ (τ : L ≃ₐ[K] L)) * (uniformizerRatio hϖ (τ : L ≃ₐ[K] L))⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, uniformizerRatio_mul]
      group
      exact mul_comm _ _
    rw [key]
    exact inv_mem h

theorem ramificationToUnits_apply (n : ℕ) (σ : lowerRamificationGroup K L n) :
    ramificationToUnits hϖ n σ =
      QuotientGroup.mk ⟨uniformizerRatio hϖ (σ : L ≃ₐ[K] L), uniformizerRatio_mem hϖ σ⟩ :=
  rfl

theorem ker_ramificationToUnits (n : ℕ) :
    (ramificationToUnits hϖ n).ker =
      (lowerRamificationGroup K L (n + 1 : ℕ)).subgroupOf (lowerRamificationGroup K L n) := by
  ext σ
  have hσ0 : (σ : L ≃ₐ[K] L) ∈ lowerRamificationGroup K L 0 :=
    lowerRamificationGroup_antitone K L (by omega) σ.2
  rw [MonoidHom.mem_ker, ramificationToUnits_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    mem_lowerRamificationGroup_iff_uniformizerRatio hϖ hσ0]

end Ratio

end GroundTheory.LocalField
end
end

section

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Polynomial IsDiscreteValuationRing IsLocalRing

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem residue_aeval_integer (p : 𝒪[K][X]) (x : 𝒪[L]) :
    residue 𝒪[L] (aeval x p) = aeval (residue 𝒪[L] x) (p.map (residue 𝒪[K])) := by
  rw [aeval_def, aeval_def, eval₂_map, hom_eval₂]
  congr 1


variable (K) in
theorem adjoin_eq_top_of_residue_of_addVal_eq_one {x : 𝒪[L]}
    (hx : Algebra.adjoin 𝓀[K] {residue 𝒪[L] x} = ⊤) {π : 𝒪[L]}
    (hπA : π ∈ Algebra.adjoin 𝒪[K] {x}) (hπ : addVal 𝒪[L] π = 1) :
    Algebra.adjoin 𝒪[K] {x} = ⊤ := by
  set A := Algebra.adjoin 𝒪[K] {x}
  set e := (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K)))

  have hres : ∀ w : 𝒪[L], ∃ a ∈ A, ∃ w', w = a + π * w' := by
    intro w
    have hw : residue 𝒪[L] w ∈ Algebra.adjoin 𝓀[K] {residue 𝒪[L] x} := by
      rw [hx]; trivial
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hw
    obtain ⟨p, hp⟩ := hw
    obtain ⟨p₀, rfl⟩ := Polynomial.map_surjective (residue 𝒪[K]) residue_surjective p
    refine ⟨aeval x p₀, ?_, ?_⟩
    · exact aeval_mem_adjoin_singleton 𝒪[K] x
    have hm : w - aeval x p₀ ∈ IsLocalRing.maximalIdeal 𝒪[L] := by
      rw [← residue_eq_zero_iff, map_sub, residue_aeval_integer]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hp
      rw [hp, sub_self]
    rw [← pow_one (IsLocalRing.maximalIdeal 𝒪[L]), mem_maximalIdeal_pow_iff_le_addVal, Nat.cast_one, ← hπ,
      addVal_le_iff_dvd] at hm
    obtain ⟨w', hw'⟩ := hm
    exact ⟨w', by rw [← hw']; ring⟩
  have step : ∀ k : ℕ, ∀ z : 𝒪[L], ∃ a ∈ A, ∃ w, z = a + π ^ k * w := by
    intro k
    induction k with
    | zero => exact fun z => ⟨0, zero_mem _, z, by simp⟩
    | succ k ih =>
      intro z
      obtain ⟨a, ha, w, rfl⟩ := ih z
      obtain ⟨b, hb, w', rfl⟩ := hres w
      refine ⟨a + π ^ k * b, add_mem ha (mul_mem (pow_mem hπA k) hb), w', ?_⟩
      ring
  obtain ⟨ϖK, hϖK⟩ := exists_irreducible 𝒪[K]
  have hassoc : Associated (algebraMap 𝒪[K] 𝒪[L] ϖK) (π ^ e) := by
    rw [← addVal_eq_iff_associated, addVal_algebraMap_integer, addVal_uniformizer hϖK,
      addVal_pow, hπ, mul_one, nsmul_eq_mul, mul_one]
  obtain ⟨u, hu⟩ := hassoc
  have hle : (⊤ : Submodule 𝒪[K] 𝒪[L]) ≤
      Subalgebra.toSubmodule A ⊔ IsLocalRing.maximalIdeal 𝒪[K] • ⊤ := by
    intro z _
    obtain ⟨a, ha, w, rfl⟩ := step e z
    refine Submodule.add_mem_sup ha ?_
    rw [← hu, mul_assoc, ← Algebra.smul_def]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [hϖK.maximalIdeal_eq]
    exact Ideal.subset_span rfl
  have hnak := Submodule.le_of_le_smul_of_le_jacobson_bot (Module.Finite.fg_top)
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hle
  rw [eq_top_iff]
  intro z _
  exact hnak Submodule.mem_top


variable (K L) in
theorem exists_integer_adjoin_eq_top : ∃ x : 𝒪[L], Algebra.adjoin 𝒪[K] {x} = ⊤ := by
  classical
  obtain ⟨ξ, hξ⟩ := Field.exists_primitive_element_of_finite_top 𝓀[K] 𝓀[L]
  have hadj : Algebra.adjoin 𝓀[K] {ξ} = ⊤ := IntermediateField.adjoin_eq_top_iff.mp hξ
  have hint : IsIntegral 𝓀[K] ξ := Algebra.IsIntegral.isIntegral ξ
  set P := minpoly 𝓀[K] ξ
  have hsep : P.Separable := PerfectField.separable_of_irreducible (minpoly.irreducible hint)
  obtain ⟨P₀, hP₀⟩ := Polynomial.map_surjective (residue 𝒪[K]) residue_surjective P
  obtain ⟨x₀, hx₀⟩ := residue_surjective ξ

  have hy₀ : aeval x₀ P₀ ∈ IsLocalRing.maximalIdeal 𝒪[L] := by
    rw [← residue_eq_zero_iff, residue_aeval_integer, hP₀, hx₀]
    exact minpoly.aeval _ _
  have hd₀ : IsUnit (aeval x₀ (derivative P₀)) := by
    rw [← not_not (a := IsUnit _), ← mem_nonunits_iff, ← mem_maximalIdeal, ← residue_eq_zero_iff,
      residue_aeval_integer, ← derivative_map, hP₀, hx₀]
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval _ _)

  obtain ⟨x, hxres, hxval⟩ : ∃ x : 𝒪[L], residue 𝒪[L] x = ξ ∧ addVal 𝒪[L] (aeval x P₀) = 1 := by
    by_cases hsq : aeval x₀ P₀ ∈ IsLocalRing.maximalIdeal 𝒪[L] ^ 2
    · obtain ⟨ϖ, hϖ⟩ := exists_irreducible 𝒪[L]
      have hϖ1 : addVal 𝒪[L] ϖ = 1 := addVal_uniformizer hϖ
      refine ⟨x₀ + ϖ, ?_, ?_⟩
      · rw [map_add (f := _), hx₀, (residue_eq_zero_iff ϖ).mpr hϖ.not_isUnit, add_zero]
      obtain ⟨k, hk⟩ := binomExpansion (P₀.map (algebraMap 𝒪[K] 𝒪[L])) x₀ ϖ
      rw [eval_map_algebraMap, eval_map_algebraMap, derivative_map, eval_map_algebraMap] at hk
      have hϖm : ϖ ∈ IsLocalRing.maximalIdeal 𝒪[L] := hϖ.not_isUnit
      have hϖsq : ϖ ^ 2 ∈ IsLocalRing.maximalIdeal 𝒪[L] ^ 2 := Ideal.pow_mem_pow hϖm 2
      refine addVal_eq_one_of_mem_of_notMem_sq ?_ ?_
      · rw [hk]
        refine add_mem (add_mem hy₀ (Ideal.mul_mem_left _ _ hϖm)) ?_
        exact Ideal.mul_mem_left _ _ (Ideal.pow_le_self two_ne_zero hϖsq)
      · intro hmem
        have h1 : aeval x₀ (derivative P₀) * ϖ ∈ IsLocalRing.maximalIdeal 𝒪[L] ^ 2 := by
          have : aeval x₀ (derivative P₀) * ϖ =
              aeval (x₀ + ϖ) P₀ - aeval x₀ P₀ - k * ϖ ^ 2 := by rw [hk]; ring
          rw [this]
          exact sub_mem (sub_mem hmem hsq) (Ideal.mul_mem_left _ _ hϖsq)
        obtain ⟨v, hv⟩ := hd₀
        have h2 : ϖ ∈ IsLocalRing.maximalIdeal 𝒪[L] ^ 2 := by
          have := Ideal.mul_mem_left (IsLocalRing.maximalIdeal 𝒪[L] ^ 2) (↑v⁻¹ : 𝒪[L]) h1
          rwa [← hv, ← mul_assoc, Units.inv_mul, one_mul] at this
        rw [mem_maximalIdeal_pow_iff_le_addVal, hϖ1] at h2
        norm_num at h2
    · exact ⟨x₀, hx₀, addVal_eq_one_of_mem_of_notMem_sq hy₀ hsq⟩
  refine ⟨x, adjoin_eq_top_of_residue_of_addVal_eq_one K (π := aeval x P₀) ?_ ?_ hxval⟩
  · rw [hxres]; exact hadj
  · exact aeval_mem_adjoin_singleton 𝒪[K] x

end GroundTheory.LocalField
end
end
