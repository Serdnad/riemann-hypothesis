module

public import GroundTheory.GlobalFields.GlobalReciprocity.InfKerDegreeLeOfLeSupZhatField
public import GroundTheory.GlobalFields.KummerTheory.Degree
public import GroundTheory.GlobalFields.IdeleGroups.LocalConditionIndex
public import GroundTheory.GlobalFields.NormResidueSymbol.RangeIdeleNormLeKerIdeleSymbol
public import Mathlib.FieldTheory.Galois.Abelian
public import GroundTheory.GlobalFields.ExistenceTheorem.PowerIndex
public import GroundTheory.GlobalFields.GlobalReciprocity.General
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.InfiniteAdeleRingMapInfiniteAdeleRingMap
import GroundTheory.GlobalFields.NormResidueSymbol.Functorial
import GroundTheory.GlobalFields.KummerTheory.Unramified
import GroundTheory.GlobalFields.NormResidueSymbol.Bundle002
public import GroundTheory.GlobalFields.PowerSubgroupIndex.Existence
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
import Mathlib.GroupTheory.Schreier
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

namespace GroundTheory.Global

open IsDedekindDomain NumberField IntermediateField IdeleGroup AdeleBaseChange

noncomputable section

section MaxAbelian

variable (K M : Type*) [Field K] [Field M] [Algebra K M]

def maxAbelian : IntermediateField K M := fixedField (commutator Gal(M/K))

variable [FiniteDimensional K M] [IsGalois K M]

instance isGalois_maxAbelian : IsGalois K (maxAbelian K M) :=
  IsGalois.of_fixedField_normal_subgroup _

instance isMulCommutative_maxAbelian : IsMulCommutative Gal(maxAbelian K M/K) := by
  refine ⟨⟨fun σ τ ↦ ?_⟩⟩
  let e : Gal(M/K) ⧸ commutator Gal(M/K) ≃* Gal(maxAbelian K M/K) :=
    IsGalois.normalAutEquivQuotient (commutator Gal(M/K))
  obtain ⟨a, rfl⟩ := e.surjective σ
  obtain ⟨b, rfl⟩ := e.surjective τ
  rw [← map_mul, ← map_mul]
  exact congrArg e (mul_comm (G := Group.Abelianization Gal(M/K)) a b)

instance isAbelianGalois_maxAbelian : IsAbelianGalois K (maxAbelian K M) where

theorem finrank_maxAbelian :
    Module.finrank K (maxAbelian K M) = Nat.card (Group.Abelianization Gal(M/K)) := by
  have h1 := Module.finrank_mul_finrank K (maxAbelian K M) M
  rw [maxAbelian, finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank K M,
    ← (commutator Gal(M/K)).card_mul_index] at h1
  have hpos : 0 < Nat.card (commutator Gal(M/K)) := Nat.card_pos
  rw [mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_left hpos h1

end MaxAbelian

namespace IdeleClassLimit

open FiniteSubfield GroundTheory.LocalField.Abstract

variable (K L : FiniteSubfield) [hKL : Fact (K ≤ L)]
  [(L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal]

theorem ker_abstractSymbol_le :
    (abstractSymbol K L).ker ≤ (FiniteSubfield.ideleClassNorm hKL.out).range := by
  intro c hc
  rw [MonoidHom.mem_ker, abstractSymbol_apply] at hc
  have hinj : Function.Injective (Group.Abelianization.map (quotientGaloisEquiv K L).toMonoidHom) :=
    fun a b hab ↦ (quotientGaloisEquiv K L).abelianizationCongr.injective hab
  rw [← map_one (Group.Abelianization.map (quotientGaloisEquiv K L).toMonoidHom), hinj.eq_iff,
    ← map_one (reciprocityEquiv K L).symm, (reciprocityEquiv K L).symm.injective.eq_iff] at hc
  change (QuotientGroup.mk (fixedEquiv K c) : tateZero IdeleClassLimit
    (K.openSubgroup : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) L.openSubgroup) = 1 at hc
  rw [QuotientGroup.eq_one_iff] at hc
  obtain ⟨b, hb⟩ := hc
  obtain ⟨d, rfl⟩ := (fixedEquiv L).surjective b
  refine ⟨d, (fixedEquiv K).injective ?_⟩
  rw [← norm_fixedEquiv hKL.out d]
  exact hb

theorem index_range_ideleClassNorm_dvd :
    (FiniteSubfield.ideleClassNorm hKL.out).range.index ∣
      Nat.card (Group.Abelianization (L.1 ≃ₐ[K.1] L.1)) := by
  refine (Subgroup.index_dvd_of_le (ker_abstractSymbol_le K L)).trans ?_
  rw [Subgroup.index_ker]
  exact Subgroup.card_subgroup_dvd_card (abstractSymbol K L).range

end IdeleClassLimit

section Transport

theorem index_range_ideleClassNorm_dvd_card_abelianization {K M : Type*} [Field K] [NumberField K]
    [Field M] [NumberField M] [Algebra K M] [IsGalois K M] :
    (ideleClassNorm K M).range.index ∣ Nat.card (Group.Abelianization Gal(M/K)) := by
  let K' := baseField K M
  let M' := topField M
  let _ : Algebra K K'.1 := (rangeMap (baseEmbedding K M)).toAlgebra
  let _ : Algebra M M'.1 := (rangeMap (embedding M)).toAlgebra
  let _ : Algebra K M'.1 := ((rangeMap (embedding M)).comp (algebraMap K M)).toAlgebra
  have : IsScalarTower K K'.1 M'.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower K M M'.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hK : Function.Bijective (algebraMap K K'.1) := rangeMap_bijective _
  have hM : Function.Bijective (algebraMap M M'.1) := rangeMap_bijective _
  have : IsGalois K M'.1 :=
    IsGalois.of_algEquiv (AlgEquiv.ofBijective (IsScalarTower.toAlgHom K M M'.1) hM)
  have : IsGalois K'.1 M'.1 := IsGalois.tower_top_of_isGalois K K'.1 M'.1
  have := FiniteSubfield.normal_subgroupOf_of_isGalois (F := K') (E := M')
  have h1 := IdeleClassLimit.index_range_ideleClassNorm_dvd K' M'
  have hrange : (ideleClassNorm K M).range =
      (ideleClassNorm K'.1 M'.1).range.map (ideleClassNorm K K'.1) := by
    ext c
    constructor
    · rintro ⟨d, rfl⟩
      refine ⟨ideleClassNorm K'.1 M'.1 (ideleClassMap M M'.1 d), ⟨_, rfl⟩, ?_⟩
      rw [ideleClassNorm_ideleClassNorm, ← ideleClassNorm_ideleClassNorm (L := M),
        ideleClassNorm_ideleClassMap, finrank_eq_one_of_bijective hM, pow_one]
    · rintro ⟨_, ⟨d, rfl⟩, rfl⟩
      exact ⟨ideleClassNorm M M'.1 d, by
        rw [ideleClassNorm_ideleClassNorm, ideleClassNorm_ideleClassNorm]⟩
  have hsurj : Function.Surjective (ideleClassNorm K K'.1) := fun c ↦
    ⟨ideleClassMap K K'.1 c, by
      rw [ideleClassNorm_ideleClassMap, finrank_eq_one_of_bijective hK, pow_one]⟩
  have hcard : Nat.card (Group.Abelianization Gal(M'.1/K'.1)) =
      Nat.card (Group.Abelianization Gal(M/K)) := by
    let f : Gal(M'.1/K'.1) →* Gal(M/K) :=
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := M'.1) M).comp (restrictScalarsHom K)
    have hinj : Function.Injective f := by
      rw [injective_iff_map_eq_one]
      intro σ hσ
      exact restrictNormal_restrictScalars_eq_one (K := K) hM hσ
    have hc : Nat.card Gal(M'.1/K'.1) = Nat.card Gal(M/K) := by
      rw [IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank]
      have e1 := Module.finrank_mul_finrank K K'.1 M'.1
      have e2 := Module.finrank_mul_finrank K M M'.1
      rw [finrank_eq_one_of_bijective hK, one_mul] at e1
      rw [finrank_eq_one_of_bijective hM, mul_one] at e2
      rw [e1, e2]
    have hbij : Function.Bijective f := hinj.bijective_of_nat_card_le hc.ge
    exact Nat.card_congr (MulEquiv.ofBijective f hbij).abelianizationCongr.toEquiv
  rw [hrange, ← hcard]
  exact (Subgroup.index_map_dvd _ hsurj).trans h1

universe u

variable {K M : Type u} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M]

theorem range_ideleClassNorm_maxAbelian :
    (ideleClassNorm K (maxAbelian K M)).range = (ideleClassNorm K M).range := by
  have hle : (ideleClassNorm K M).range ≤ (ideleClassNorm K (maxAbelian K M)).range := by
    rintro _ ⟨c, rfl⟩
    exact ⟨ideleClassNorm (maxAbelian K M) M c, ideleClassNorm_ideleClassNorm c⟩
  have hE : (ideleClassNorm K (maxAbelian K M)).range.index =
      Nat.card (Group.Abelianization Gal(M/K)) := by
    rw [index_range_ideleClassNorm_eq_finrank_of_isMulCommutative, finrank_maxAbelian]
  have hne : (ideleClassNorm K (maxAbelian K M)).range.index ≠ 0 := by
    rw [index_range_ideleClassNorm_eq_finrank_of_isMulCommutative]
    exact Module.finrank_pos.ne'
  have heq : (ideleClassNorm K M).range.index = (ideleClassNorm K (maxAbelian K M)).range.index :=
    Nat.dvd_antisymm (hE ▸ index_range_ideleClassNorm_dvd_card_abelianization)
      (Subgroup.index_dvd_of_le hle)
  have hrel := Subgroup.relIndex_mul_index hle
  rw [heq] at hrel
  have h1 : (ideleClassNorm K M).range.relIndex (ideleClassNorm K (maxAbelian K M)).range = 1 := by
    have := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) (hrel.trans (one_mul _).symm)
    exact this
  exact le_antisymm (Subgroup.relIndex_eq_one.1 h1) hle


omit [IsGalois K M] in
theorem exists_isAbelianGalois_range_ideleClassNorm_le (L : Type u) [Field L] [NumberField L]
    [Algebra K L] :
    ∃ (E : Type u) (_ : Field E) (_ : NumberField E) (_ : Algebra K E),
      IsAbelianGalois K E ∧ (ideleClassNorm K E).range ≤ (ideleClassNorm K L).range := by
  let Ω := AlgebraicClosure L
  have : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.trans K L Ω
  have : IsAlgClosure K Ω := ⟨AlgebraicClosure.isAlgClosed L, inferInstance⟩
  let N := normalClosure K L Ω
  have : IsGalois K N := ⟨⟩
  have : NumberField N := NumberField.of_module_finite K N
  refine ⟨maxAbelian K N, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  rw [range_ideleClassNorm_maxAbelian]
  rintro _ ⟨c, rfl⟩
  exact ⟨ideleClassNorm L N c, ideleClassNorm_ideleClassNorm c⟩

end Transport

end

end GroundTheory.Global
end

section

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IdeleGroup IntermediateField
  GroundTheory.ProfCoh SemiLocal

noncomputable section

universe u

theorem IdeleGroup.finiteProj_mem_units_of_ord_eq_zero {K : Type*} [Field K] [NumberField K]
    {v : HeightOneSpectrum (𝓞 K)} {x : IdeleGroup K} (h : ord v x = 0) :
    finiteProj v x ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  rw [ord_eq_zero_iff] at h
  refine (Submonoid.mem_units_iff _ _).2 ⟨?_, ?_⟩
  · rw [coe_finiteProj]
    exact h.1
  · rw [← map_inv, coe_finiteProj]
    exact h.2

section SUnits

variable {K : Type u} [Field K] [NumberField K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]


omit [HasEnoughRootsOfUnity K n] in
theorem unitsPow_subgroupOf_sUnit (S : Set (HeightOneSpectrum (𝓞 K))) :
    (unitsPow K n).subgroupOf (S.unit K) = (powMonoidHom n : S.unit K →* S.unit K).range := by
  ext e
  rw [Subgroup.mem_subgroupOf, mem_unitsPow, MonoidHom.mem_range]
  constructor
  · rintro ⟨z, hz⟩
    have hzu : z ∈ S.unit K := by
      intro v hv
      have he : v.valuationOfNeZero (e : Kˣ) = 1 := by
        have h := e.2 v hv
        rw [← valuationOfNeZero_eq] at h
        exact_mod_cast h
      have h1 : v.valuationOfNeZero z ^ n = 1 := by rw [← map_pow, hz, he]
      rw [← valuationOfNeZero_eq, (pow_eq_one_iff.1 h1).resolve_right (NeZero.ne n),
        WithZero.coe_one]
    exact ⟨⟨z, hzu⟩, Subtype.ext hz⟩
  · rintro ⟨f, rfl⟩
    exact ⟨f, rfl⟩

theorem index_unitsPow_subgroupOf_sUnit (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] :
    ((unitsPow K n).subgroupOf (S.unit K)).index =
      n ^ (Fintype.card (InfinitePlace K) + Nat.card S) := by
  rw [unitsPow_subgroupOf_sUnit, SUnit.index_range_powMonoidHom]

instance finiteIndex_unitsPow_subgroupOf_sUnit (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] :
    ((unitsPow K n).subgroupOf (S.unit K)).FiniteIndex :=
  ⟨by rw [index_unitsPow_subgroupOf_sUnit]; exact pow_ne_zero _ (NeZero.ne n)⟩


variable (K) in
abbrev sUnitKummerField (S : Set (HeightOneSpectrum (𝓞 K))) :
    IntermediateField K (AlgebraicClosure K) :=
  kummerExtension K n (AlgebraicClosure K) (S.unit K)

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]

instance sUnitKummerField.numberField : NumberField (sUnitKummerField K n S) :=
  NumberField.of_module_finite K _

instance sUnitKummerField.isAbelianGalois : IsAbelianGalois K (sUnitKummerField K n S) :=
  { toIsGalois := inferInstance, toIsMulCommutative := inferInstance }

theorem finrank_sUnitKummerField :
    Module.finrank K (sUnitKummerField K n S) =
      n ^ (Fintype.card (InfinitePlace K) + Nat.card S) := by
  rw [finrank_kummerExtension, ← Subgroup.index, index_unitsPow_subgroupOf_sUnit]

end SUnits

section Symbol

attribute [local instance] galCommGroup

variable {K : Type u} [Field K] [NumberField K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S]

theorem ideleSymbol_adjoin_eq_one
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    {a : Kˣ} (ha : a ∈ S.unit K) (β : sUnitKummerField K n S)
    (hβ : β ^ n = algebraMap K _ (a : K)) {x : IdeleGroup K} (hx : x ∈ powerSubgroup n S ∅) :
    ideleSymbol K (K⟮β⟯ : IntermediateField K (sUnitKummerField K n S)) x = 1 := by
  have hexpM : ∀ τ : Gal(sUnitKummerField K n S/K), τ ^ n = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (kummerExtension_exponent_dvd K n _ _)
  have hexp : ∀ τ : Gal(K⟮β⟯/K), τ ^ n = 1 := by
    intro τ
    obtain ⟨τ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := K⟮β⟯)
      (E := sUnitKummerField K n S) τ
    rw [← map_pow, hexpM, map_one]
  have hβ' : (⟨β, mem_adjoin_simple_self K β⟩ : K⟮β⟯) ^ n = algebraMap K K⟮β⟯ (a : K) :=
    Subtype.ext (by exact hβ)
  have hgen : adjoin K {(⟨β, mem_adjoin_simple_self K β⟩ : K⟮β⟯)} = ⊤ :=
    lift_injective _ (by rw [lift_adjoin_simple, lift_top])
  have hinf : ∀ w, infiniteLocalSymbol K⟮β⟯ w (infiniteProj w x) = 1 := by
    intro w
    obtain ⟨t, ht⟩ := hx.2.1 w
    rw [← ht, powMonoidHom_apply, map_pow, hexp]
  have hfin : ∀ v, localSymbol K⟮β⟯ v (finiteProj v x) = 1 := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨t, ht⟩ := hx.1 v hv
      rw [← ht, powMonoidHom_apply, map_pow, hexp]
    · have hord : ord v x = 0 := hx.2.2 v (by simpa using hv)
      obtain ⟨w⟩ := nonempty_placesOver K⟮β⟯ v
      have hnv : (n : 𝓞 K) ∉ v.asIdeal := fun h ↦ hv (hS v h)
      have hav : (n : ℤ) ∣ WithZero.log (v.valuation K (a : K)) := by
        have h := ha v hv
        rw [← valuationOfNeZero_eq] at h
        rw [← valuationOfNeZero_eq, show v.valuationOfNeZero a = 1 by exact_mod_cast h]
        simp
      have he := Kummer.ramificationIdx_eq_one_of_pow_eq (M := K⟮β⟯) a hβ' hgen v hnv hav
        w.1.asIdeal
      exact units_le_ker_localSymbol K⟮β⟯ v w he (finiteProj_mem_units_of_ord_eq_zero hord)
  rw [ideleSymbol_apply, finprod_eq_one_of_forall_eq_one hfin,
    Finset.prod_eq_one fun w _ ↦ hinf w, mul_one]

theorem ideleSymbol_sUnitKummerField_eq_one
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    {x : IdeleGroup K} (hx : x ∈ powerSubgroup n S ∅) :
    ideleSymbol K (sUnitKummerField K n S) x = 1 := by
  set M := sUnitKummerField K n S
  have hfix : ∀ (β : M) (a : Kˣ), a ∈ S.unit K →
      (β : AlgebraicClosure K) ^ n = algebraMap K _ (a : K) → ideleSymbol K M x β = β := by
    intro β a ha hβ
    have hβ' : β ^ n = algebraMap K M (a : K) := Subtype.ext hβ
    have h1 := restrictNormal_ideleSymbol (K⟮β⟯ : IntermediateField K M) M x
    rw [ideleSymbol_adjoin_eq_one hS ha β hβ' hx, AlgEquiv.restrictNormal_eq_one_iff] at h1
    exact h1 β (mem_adjoin_simple_self K β)
  apply AlgEquiv.coe_toAlgHom_injective
  refine IntermediateField.algHom_ext_of_eq_adjoin K (S := M)
    (s := {α : AlgebraicClosure K | ∃ a ∈ S.unit K, α ^ n = algebraMap K _ (a : K)}) rfl ?_
  rintro y ⟨a, ha, hy⟩
  exact hfix _ a ha hy

theorem map_powerSubgroup_le_range_ideleClassNorm
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (powerSubgroup n S ∅).map (IdeleClassGroup.mk K) ≤
      (ideleClassNorm K (sUnitKummerField K n S)).range := by
  rw [← ker_reciprocityMap, Subgroup.map_le_iff_le_comap]
  intro x hx
  rw [Subgroup.mem_comap, MonoidHom.mem_ker, reciprocityMap_mk]
  exact ideleSymbol_sUnitKummerField_eq_one hS hx

theorem range_ideleClassNorm_sUnitKummerField (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hJ : (diagonal K).range ⊔ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤) :
    (ideleClassNorm K (sUnitKummerField K n (S : Set (HeightOneSpectrum (𝓞 K))))).range =
      (powerSubgroup n (S : Set (HeightOneSpectrum (𝓞 K))) ∅).map (IdeleClassGroup.mk K) := by
  have hle := map_powerSubgroup_le_range_ideleClassNorm (n := n)
    (S := (S : Set (HeightOneSpectrum (𝓞 K)))) fun v hv ↦ Finset.mem_coe.2 (hS v hv)
  have h1 : (ideleClassNorm K (sUnitKummerField K n (S : Set (HeightOneSpectrum (𝓞 K))))).range.index =
      n ^ (S.card + Fintype.card (InfinitePlace K)) := by
    rw [index_range_ideleClassNorm_eq_finrank_of_isMulCommutative, finrank_sUnitKummerField,
      Nat.card_coe_set_eq, Set.ncard_coe_finset, add_comm]
  have h2 := index_map_powerSubgroup (n := n) S hS hJ
  have hrel := Subgroup.relIndex_mul_index hle
  rw [h1, h2] at hrel
  have hone : ((powerSubgroup n (S : Set (HeightOneSpectrum (𝓞 K))) ∅).map
      (IdeleClassGroup.mk K)).relIndex
      (ideleClassNorm K (sUnitKummerField K n (S : Set (HeightOneSpectrum (𝓞 K))))).range = 1 :=
    Nat.eq_of_mul_eq_mul_right (pow_pos (NeZero.pos n) _) (by rw [hrel, one_mul])
  exact le_antisymm (Subgroup.relIndex_eq_one.1 hone) hle

end Symbol

end

end GroundTheory.Global
end
