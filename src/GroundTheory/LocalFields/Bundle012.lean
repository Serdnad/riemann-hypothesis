module

public import GroundTheory.LocalFields.AbstractLocalReciprocity.ReciprocityAbelianizationRestrictReciprocityLimi
import GroundTheory.LocalFields.AbstractLocalReciprocity.Functoriality
public import GroundTheory.LocalFields.LubinTateReciprocity
public import GroundTheory.LocalFields.ExistenceDictionary
import GroundTheory.LocalFields.LocalReciprocityFinite
public import GroundTheory.LocalFields.Bundle008
public import GroundTheory.LocalFields.LubinTateLimitGalois
public import GroundTheory.LocalFields.LubinTateUnramified
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.LocalFields.AbstractLocalReciprocity.NormGroups

@[expose] public section

section

namespace GroundTheory.LocalField.Abstract

section TopologicalAbelianization

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
  [TopologicalSpace H] [IsTopologicalGroup H]

theorem topologicalClosure_commutator_le_comap (f : G →* H) (hf : Continuous f) :
    (commutator G).topologicalClosure ≤ (commutator H).topologicalClosure.comap f := by
  refine Subgroup.topologicalClosure_minimal _ ?_
    ((Subgroup.isClosed_topologicalClosure _).preimage hf)
  rw [commutator, Subgroup.commutator_le]
  intro a _ b _
  rw [Subgroup.mem_comap, map_commutatorElement]
  exact Subgroup.le_topologicalClosure _
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))

def topologicalAbelianizationMap (f : G →* H) (hf : Continuous f) :
    TopologicalAbelianization G →* TopologicalAbelianization H :=
  QuotientGroup.map _ _ f (topologicalClosure_commutator_le_comap f hf)

theorem continuous_topologicalAbelianizationMap (f : G →* H) (hf : Continuous f) :
    Continuous (topologicalAbelianizationMap f hf) := by
  rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
  exact (QuotientGroup.isQuotientMap_mk _).continuous.comp hf

end TopologicalAbelianization

section Maps

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
theorem continuous_inclusion {K K' : Subgroup G} (hK : K' ≤ K) :
    Continuous (Subgroup.inclusion hK) :=
  continuous_subtype_val.subtype_mk _

def limitRestrict {K K' : OpenSubgroup G} (hK : K' ≤ K) :
    TopologicalAbelianization (K' : Subgroup G) →* TopologicalAbelianization (K : Subgroup G) :=
  topologicalAbelianizationMap (Subgroup.inclusion hK) (continuous_inclusion hK)

@[simp]
theorem limitRestrict_mk {K K' : OpenSubgroup G} (hK : K' ≤ K) (g : (K' : Subgroup G)) :
    limitRestrict hK (g : TopologicalAbelianization (K' : Subgroup G)) =
      ((⟨g, hK g.2⟩ : (K : Subgroup G)) : TopologicalAbelianization (K : Subgroup G)) :=
  rfl

end Maps

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  (D : ClassFieldData G A) (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

theorem limitRestrict_reciprocityLimit {K K' : OpenSubgroup G} (hK : K' ≤ K)
    (a : fixedModule A (K' : Subgroup G)) :
    limitRestrict hK (D.reciprocityLimit hax K' a) =
      D.reciprocityLimit hax K (norm A (K : Subgroup G) (K' : Subgroup G) a) := by
  refine D.eq_reciprocityLimit hax fun L hL _ => ?_
  have hmap : (commutator (K' : Subgroup G)).map (Subgroup.inclusion hK) ≤
      commutator (K : Subgroup G) := by
    rw [commutator, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have hL' : IsAbelianExtension K' (L ⊓ K') := by
    refine ⟨inf_le_right, fun x hx => ?_⟩
    rw [Subgroup.mem_subgroupOf]
    refine ⟨?_, x.2⟩
    have h1 := hL.commutator_le (hmap ⟨x, hx, rfl⟩)
    rw [Subgroup.mem_subgroupOf] at h1
    exact h1
  have := hL'.normal
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (D.reciprocityLimit hax K' a)
  have e := D.reciprocity_abelianizationRestrict_reciprocityLimit hax hL' a
  rw [← hg, abelianizationRestrict_mk] at e
  rw [← hg, limitRestrict_mk, abelianizationRestrict_mk]
  have h := D.reciprocity_galRestrict hax hL.le hL'.le hK inf_le_left
    (g : (K' : Subgroup G) ⧸ ((L ⊓ K' : OpenSubgroup G) : Subgroup G).subgroupOf K')
  rw [galRestrict_mk, e, normTateZero_mk] at h
  exact h

end ClassFieldData

end GroundTheory.LocalField.Abstract
end

section

noncomputable section

open ValuativeRel GroundTheory.LocalField.FormalGroup

namespace GroundTheory.LocalField

open Abstract

section LubinTate

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]
  {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]} (hf : IsLubinTateSeries π f)

attribute [local instance] isDiscreteModule_units

theorem lubinTateField_mul_comm (n : ℕ)
    (σ τ : lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n) : σ * τ = τ * σ := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  apply (lubinTateGalEquiv hπ hf n).injective
  rw [map_mul, map_mul]
  exact mul_comm (G := (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ) _ _


include hf in
theorem mem_unitFiltration_of_mem_range_normUnits {n : ℕ} (hn : 0 < n) (u : 𝒪[K]ˣ) (k : ℤ)
    (h : unitUniformizerPow hπ u k ∈ (normUnits K (lubinTateField Ω hπ hf n)).range) :
    u ∈ unitFiltration K n := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  set T := lubinTateField Ω hπ hf n
  haveI : IsGalois K T :=
    IsGalois.of_card_aut_eq_finrank K _
      ((Nat.card_congr (lubinTateGalEquiv (Ω := Ω) hπ hf n).toEquiv).trans
        (card_units_quotient_eq_finrank (Ω := Ω) (hπ := hπ) hf n))
  have hab : IsAbelianExtension ⊤ (fixingOpenSubgroup T) :=
    (isAbelianExtension_fixingOpenSubgroup_iff T).2 ⟨inferInstance, lubinTateField_mul_comm hπ hf n⟩
  have := hab.normal
  obtain ⟨τ, hτd, hτ⟩ := exists_lubinTate_action (Ω := Ω) hπ hf hn u k
  have hr := reciprocity_lubinTate hπ hf hn (fixingOpenSubgroup T)
    (by rw [coe_fixingOpenSubgroup]) (by rw [coe_fixingOpenSubgroup]; exact inf_le_left) u k τ hτd hτ
  have hmem : τ ∈ (fixingOpenSubgroup T : Subgroup (Ω ≃ₐ[K] Ω)) := by
    refine ((localClassFieldTheory K Ω).mem_normGroup_iff_of_reciprocity
      (localClassFieldTheory K Ω).classFieldAxiom hab hr).1 ?_
    rw [mem_normGroup_iff_mem_range_normUnits, MulEquiv.apply_symm_apply]
    exact h
  rw [coe_fixingOpenSubgroup] at hmem

  have hchar := lubinTateChar_eq_of_apply hπ hf (le_refl T) 1 ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) fun x hx => by
    have e := congrArg IdealPoint.val (hτ x hx)
    rw [lubinTateGalPointMap_val] at e
    rw [← e, AlgEquiv.one_apply]
    exact ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem _
      (val_mem_lubinTateField hπ hf hx)).symm
  rw [map_one, Units.val_one] at hchar
  have h1 : unitsMk π n u⁻¹ = 1 := Units.ext (by rw [coe_unitsMk, Units.val_one, hchar])
  exact inv_mem_iff.1 ((unitsMk_eq_one_iff hπ).1 h1)


omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] in
theorem range_normUnits_anti {L L' : IntermediateField K Ω} [FiniteDimensional K L]
    [FiniteDimensional K L'] (h : L ≤ L') : (normUnits K L').range ≤ (normUnits K L).range := by
  rw [← map_baseUnitsEquiv_normGroup, ← map_baseUnitsEquiv_normGroup]
  exact Subgroup.map_mono (normGroup_mono (fixingOpenSubgroup_anti h) le_top)


omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem unitUniformizerPow_eq (u : 𝒪[K]ˣ) (k : ℤ) :
    unitUniformizerPow hπ u k = uniformizerUnit hπ ^ k * unitsIncl K u := by
  rw [unitUniformizerPow, mul_comm]
  rfl


include hf in
theorem range_normUnits_sup_le {n m : ℕ} (hn : 0 < n) {E : IntermediateField K Ω}
    (hE : IsUnramifiedSubextension E) (hmE : m ∣ Module.finrank K E) {H : Subgroup Kˣ}
    (hnH : unitFiltrationUnits K n ≤ H) (hmH : (powMonoidHom m : Kˣ →* Kˣ).range ≤ H) :
    (normUnits K (lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω)).range ≤ H := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have := hE.1
  set T := lubinTateField Ω hπ hf n
  set L : IntermediateField K Ω := T ⊔ E
  rintro _ ⟨y, rfl⟩

  have hdvd : m ∣ ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) := by
    have h1 := residueDegree_dvd_of_le (le_sup_right : E ≤ L)
    rw [residueDegree_eq_finrank_of_unramified K E hE.ramificationIndex_eq_one] at h1
    exact hmE.trans h1
  obtain ⟨j, hj⟩ := hdvd
  obtain ⟨⟨k, u⟩, hx⟩ := (unitsOfIntProd_bijective hπ).2 (normUnits K L y)
  have hk : k.toAdd = (m : ℤ) * ((j : ℤ) * ord ((y : L) : L)) := by
    rw [← ord_unitsOfIntProd hπ k u, hx, coe_normUnits, ord_norm, hj]
    push_cast
    ring
  have hxu : unitUniformizerPow hπ u k.toAdd = normUnits K L y := by
    rw [← hx, unitsOfIntProd_eq, unitUniformizerPow_eq]

  have hT : unitUniformizerPow hπ u k.toAdd ∈ (normUnits K T).range := by
    rw [hxu]
    exact range_normUnits_anti le_sup_left ⟨y, rfl⟩
  have hu := mem_unitFiltration_of_mem_range_normUnits hπ hf hn u k.toAdd hT
  rw [← hxu, unitUniformizerPow_eq]
  refine H.mul_mem (hmH ⟨uniformizerUnit hπ ^ ((j : ℤ) * ord ((y : L) : L)), ?_⟩)
    (hnH ⟨u, hu, rfl⟩)
  rw [powMonoidHom_apply, ← zpow_natCast, ← zpow_mul, hk, mul_comm]

end LubinTate

section Existence

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

attribute [local instance] isDiscreteModule_units

theorem exists_range_normUnits_le (H : Subgroup Kˣ) [H.FiniteIndex] (hH : IsOpen (H : Set Kˣ)) :
    ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L), (normUnits K L).range ≤ H := by
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  obtain ⟨⟨n, hnH⟩, m, hm, hmH⟩ := exists_unitFiltrationUnits_le_and_range_pow_le hH
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hE := isUnramifiedSubextension_unramifiedTower (K := K) (Ω := Ω) m
  have := hE.1
  have hmE : m ∣ Module.finrank K (unramifiedTower K Ω m) := by
    rw [finrank_unramifiedTower]
    exact Nat.dvd_factorial (Nat.pos_of_ne_zero hm) m.le_succ
  have hf : IsLubinTateSeries π (ltPoly π : PowerSeries 𝒪[K]) := by
    have hq := one_lt_card_residueField' K
    refine ⟨?_, ?_, ?_⟩
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, ltPoly]
      simp [Polynomial.coeff_X_pow, show 0 ≠ Nat.card 𝓀[K] by omega]
    · rw [Polynomial.coeff_coe, ltPoly]
      simp [Polynomial.coeff_X_pow, hq.ne]
    · intro k
      rw [coeff_ltPoly_sub, Polynomial.coeff_C_mul_X]
      split_ifs
      · exact dvd_rfl
      · exact dvd_zero π
  exact ⟨_, inferInstance, range_normUnits_sup_le hπ hf n.succ_pos hE hmE
    ((unitFiltrationUnits_antitone n.le_succ).trans hnH) hmH⟩

theorem isOpen_range_normUnits_and_finiteIndex (L : IntermediateField K Ω) [FiniteDimensional K L] :
    IsOpen ((normUnits K L).range : Set Kˣ) ∧ (normUnits K L).range.FiniteIndex := by
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  have : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L Ω
  exact ⟨isOpen_range_normUnits K L, finiteIndex_range_normUnits K L⟩

theorem exists_range_normUnits_eq (H : Subgroup Kˣ) [H.FiniteIndex] (hH : IsOpen (H : Set Kˣ)) :
    ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L), IsGalois K L ∧
      (∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) ∧ (normUnits K L).range = H := by
  obtain ⟨L₀, _, hL₀⟩ := exists_range_normUnits_le (Ω := Ω) H hH
  set B := H.comap (baseUnitsEquiv (K := K) (Ω := Ω) :
    fixedModule Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω)) →* Kˣ)
  have hB : normGroup Ωˣ ⊤ (fixingOpenSubgroup L₀) ≤ B := by
    rw [normGroup_eq_comap]
    exact Subgroup.comap_mono hL₀
  obtain ⟨U, hU, -, hUB⟩ := (localClassFieldTheory K Ω).exists_normGroup_eq_of_le
    (localClassFieldTheory K Ω).classFieldAxiom le_top hB
  set M := IntermediateField.fixedField (U : Subgroup (Ω ≃ₐ[K] Ω))
  have hMU : fixingOpenSubgroup M = U := fixingOpenSubgroup_fixedField U
  rw [← hMU] at hU hUB
  obtain ⟨hG, hc⟩ := (isAbelianExtension_fixingOpenSubgroup_iff M).1 hU
  refine ⟨M, inferInstance, hG, hc, ?_⟩
  rw [← map_baseUnitsEquiv_normGroup, hUB]
  exact Subgroup.map_comap_eq_self_of_surjective baseUnitsEquiv.surjective H

end Existence

end GroundTheory.LocalField
end
end
