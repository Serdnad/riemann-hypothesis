module

public import GroundTheory.GlobalFields.HerbrandQuotients.CycTate
public import GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsOpenSubgroupMemFixedModule
public import GroundTheory.LocalFields.CompleteTrivial
public import GroundTheory.LocalFields.Integers
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

namespace GroundTheory.LocalField

open GroundTheory.GroupCoh GroundTheory.Global

variable {G M : Type*} [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]

theorem toMul_cycNorm (x : Additive M) :
    (cycNorm (Representation.ofMulDistribMulAction G M) x).toMul = tateNorm G M x.toMul := by
  rw [cycNorm_apply, toMul_sum, tateNorm_apply]
  rfl


omit [Fintype G] in
theorem toMul_cycSubOne (σ : G) (x : Additive M) :
    (cycSubOne (Representation.ofMulDistribMulAction G M) σ x).toMul = σ • x.toMul / x.toMul := by
  rw [cycSubOne_apply]
  rfl

theorem ker_cycNorm_ofMulDistribMulAction :
    (cycNorm (Representation.ofMulDistribMulAction G M)).ker = (tateNorm G M).ker.toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_ker, Additive.mem_toAddSubgroup, MonoidHom.mem_ker, ← toMul_cycNorm]
  exact ⟨fun h => by rw [h]; rfl, fun h => by rw [← toMul_zero] at h; exact Additive.toMul.injective h⟩

theorem range_cycNorm_ofMulDistribMulAction :
    (cycNorm (Representation.ofMulDistribMulAction G M)).range =
      (tateNorm G M).range.toAddSubgroup := by
  ext y
  rw [AddMonoidHom.mem_range, Additive.mem_toAddSubgroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.toMul, (toMul_cycNorm x).symm⟩
  · rintro ⟨x, hx⟩
    refine ⟨Additive.ofMul x, Additive.toMul.injective ?_⟩
    rw [toMul_cycNorm]
    exact hx

variable {σ : G}


omit [Fintype G] in
theorem ker_cycSubOne_ofMulDistribMulAction (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    (cycSubOne (Representation.ofMulDistribMulAction G M) σ).ker =
      (invariants G M).toAddSubgroup := by
  ext x
  rw [mem_ker_cycSubOne_iff _ hσ, Additive.mem_toAddSubgroup, mem_invariants]
  simp only [Representation.ofMulDistribMulAction_apply_apply]
  exact ⟨fun h g => congrArg Additive.toMul (h g), fun h g => by rw [h g]; rfl⟩


omit [Fintype G] in
theorem range_cycSubOne_ofMulDistribMulAction (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    (cycSubOne (Representation.ofMulDistribMulAction G M) σ).range =
      (augmentation G M).toAddSubgroup := by
  rw [range_cycSubOne_eq_closure _ hσ, augmentation, Subgroup.toAddSubgroup_closure]
  congr 1

theorem natCard_tateZero_eq (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (TateZero G M) =
      Nat.card (CycTateZero (Representation.ofMulDistribMulAction G M) σ) := by
  change (tateNorm G M).range.relIndex (invariants G M) =
    (cycNorm (Representation.ofMulDistribMulAction G M)).range.relIndex
      (cycSubOne (Representation.ofMulDistribMulAction G M) σ).ker
  rw [ker_cycSubOne_ofMulDistribMulAction hσ, range_cycNorm_ofMulDistribMulAction,
    Subgroup.relIndex_toAddSubgroup]

theorem natCard_tateNegOne_eq (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (TateNegOne G M) =
      Nat.card (CycTateNegOne (Representation.ofMulDistribMulAction G M) σ) := by
  change (augmentation G M).relIndex (tateNorm G M).ker =
    (cycSubOne (Representation.ofMulDistribMulAction G M) σ).range.relIndex
      (cycNorm (Representation.ofMulDistribMulAction G M)).ker
  rw [range_cycSubOne_ofMulDistribMulAction hσ, ker_cycNorm_ofMulDistribMulAction,
    Subgroup.relIndex_toAddSubgroup]

theorem cycHerbrand_ofMulDistribMulAction (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cycHerbrand (Representation.ofMulDistribMulAction G M) σ =
      (Nat.card (TateZero G M) : ℚ) / Nat.card (TateNegOne G M) := by
  rw [cycHerbrand_eq, natCard_tateZero_eq hσ, natCard_tateNegOne_eq hσ]

private theorem finite_iff_natCard_ne_zero {X : Type*} [Nonempty X] :
    Finite X ↔ Nat.card X ≠ 0 := by
  rw [Nat.card_ne_zero]
  exact ⟨fun h => ⟨inferInstance, h⟩, fun h => h.2⟩

theorem hasHerbrandQuotient_iff (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient (cycSubOne (Representation.ofMulDistribMulAction G M) σ)
        (cycNorm (Representation.ofMulDistribMulAction G M)) ↔
      Finite (TateZero G M) ∧ Finite (TateNegOne G M) := by
  rw [HasHerbrandQuotient, finite_iff_natCard_ne_zero, finite_iff_natCard_ne_zero,
    finite_iff_natCard_ne_zero (X := TateZero G M), finite_iff_natCard_ne_zero (X := TateNegOne G M),
    natCard_tateZero_eq hσ, natCard_tateNegOne_eq hσ]

theorem cycHerbrand_eq_one_of_subsingleton (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    [Subsingleton (TateZero G M)] [Subsingleton (TateNegOne G M)] :
    HasHerbrandQuotient (cycSubOne (Representation.ofMulDistribMulAction G M) σ)
        (cycNorm (Representation.ofMulDistribMulAction G M)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction G M) σ = 1 := by
  refine ⟨(hasHerbrandQuotient_iff hσ).mpr ⟨inferInstance, inferInstance⟩, ?_⟩
  rw [cycHerbrand_ofMulDistribMulAction hσ, Nat.card_unique, Nat.card_unique]
  norm_num

section Injective

variable {N : Type*} [CommGroup N] [MulDistribMulAction G N]


omit [Fintype G] in
theorem toAdditive_cycSubOne (i : M →* N) (hi : ∀ (g : G) (x : M), i (g • x) = g • i x) (τ : G)
    (x : Additive M) :
    MonoidHom.toAdditive i (cycSubOne (Representation.ofMulDistribMulAction G M) τ x) =
      cycSubOne (Representation.ofMulDistribMulAction G N) τ (MonoidHom.toAdditive i x) := by
  apply Additive.toMul.injective
  rw [toMul_cycSubOne]
  change i (cycSubOne (Representation.ofMulDistribMulAction G M) τ x).toMul = _
  rw [toMul_cycSubOne, map_div, hi]
  rfl

theorem toAdditive_cycNorm (i : M →* N) (hi : ∀ (g : G) (x : M), i (g • x) = g • i x)
    (x : Additive M) :
    MonoidHom.toAdditive i (cycNorm (Representation.ofMulDistribMulAction G M) x) =
      cycNorm (Representation.ofMulDistribMulAction G N) (MonoidHom.toAdditive i x) := by
  apply Additive.toMul.injective
  rw [toMul_cycNorm]
  change i (cycNorm (Representation.ofMulDistribMulAction G M) x).toMul = _
  rw [toMul_cycNorm, tateNorm_apply, tateNorm_apply, map_prod]
  simp_rw [hi]
  rfl

private theorem range_toAdditive (i : M →* N) :
    (MonoidHom.toAdditive i).range = i.range.toAddSubgroup := by
  ext y
  rw [AddMonoidHom.mem_range, Additive.mem_toAddSubgroup, MonoidHom.mem_range]
  exact ⟨fun ⟨x, hx⟩ => ⟨x.toMul, by rw [← hx]; rfl⟩,
    fun ⟨x, hx⟩ => ⟨Additive.ofMul x, Additive.toMul.injective hx⟩⟩

theorem cycHerbrand_eq_of_injective (i : M →* N) (hinj : Function.Injective i)
    (hi : ∀ (g : G) (x : M), i (g • x) = g • i x) [i.range.FiniteIndex] (τ : G) :
    (HasHerbrandQuotient (cycSubOne (Representation.ofMulDistribMulAction G M) τ)
        (cycNorm (Representation.ofMulDistribMulAction G M)) ↔
      HasHerbrandQuotient (cycSubOne (Representation.ofMulDistribMulAction G N) τ)
        (cycNorm (Representation.ofMulDistribMulAction G N))) ∧
    cycHerbrand (Representation.ofMulDistribMulAction G M) τ =
      cycHerbrand (Representation.ofMulDistribMulAction G N) τ := by
  have hfi : (MonoidHom.toAdditive i).range.FiniteIndex := by
    constructor
    rw [range_toAdditive, Subgroup.index_toAddSubgroup]
    exact Subgroup.FiniteIndex.index_ne_zero
  have : Finite (Additive N ⧸ (MonoidHom.toAdditive i).range) :=
    AddSubgroup.finite_quotient_of_finiteIndex
  have hinj' : Function.Injective (MonoidHom.toAdditive i) := hinj
  exact ⟨hasHerbrandQuotient_iff_of_injective_of_finite hinj' (toAdditive_cycSubOne i hi τ)
      (toAdditive_cycNorm i hi) (cycSubOne_cycNorm _ τ) (cycNorm_cycSubOne _ τ),
    herbrandQuotient_eq_of_injective_of_finite hinj' (toAdditive_cycSubOne i hi τ)
      (toAdditive_cycNorm i hi) (cycSubOne_cycNorm _ τ) (cycNorm_cycSubOne _ τ)⟩

end Injective

end GroundTheory.LocalField
end

section

namespace GroundTheory.LocalField.Abstract

open GroundTheory.LocalField (tateNorm invariants mem_invariants TateZero TateNegOne)

section Model

variable {G : Type*} [Group G] (A : Type*) [CommGroup A] [MulDistribMulAction G A]
  (K L : Subgroup G) (Γ : Type*) [Group Γ] (M : Type*) [CommGroup M] [MulDistribMulAction Γ M]

structure TateModel where
  le : L ≤ K

  hom : K →* Γ
  surjective_hom : Function.Surjective hom
  ker_hom : hom.ker = L.subgroupOf K

  equiv : fixedModule A L ≃* M

  coe_equiv_symm_smul : ∀ (σ : K) (a : fixedModule A L),
    ((equiv.symm (hom σ • equiv a) : fixedModule A L) : A) = (σ : G) • (a : A)

namespace TateModel

variable {A K L Γ M} (T : TateModel A K L Γ M)


theorem equiv_smul (σ : K) (a : fixedModule A L) (h : (σ : G) • (a : A) ∈ fixedModule A L) :
    T.equiv ⟨(σ : G) • (a : A), h⟩ = T.hom σ • T.equiv a := by
  rw [← T.equiv.apply_symm_apply (T.hom σ • T.equiv a)]
  congr 1
  exact Subtype.ext (T.coe_equiv_symm_smul σ a).symm

theorem mem_fixedModule_iff (a : fixedModule A L) :
    (a : A) ∈ fixedModule A K ↔ T.equiv a ∈ invariants Γ M := by
  constructor
  · intro ha γ
    obtain ⟨σ, rfl⟩ := T.surjective_hom γ
    have h : T.equiv.symm (T.hom σ • T.equiv a) = a :=
      Subtype.ext ((T.coe_equiv_symm_smul σ a).trans (ha σ σ.2))
    rw [← T.equiv.apply_symm_apply (T.hom σ • T.equiv a), h]
  · intro ha σ hσ
    rw [← T.coe_equiv_symm_smul ⟨σ, hσ⟩ a, ha, MulEquiv.symm_apply_apply]

def fixedModuleEquiv : fixedModule A K ≃* invariants Γ M where
  toFun a := ⟨T.equiv ⟨a, fixedModule_anti T.le a.2⟩,
    (T.mem_fixedModule_iff ⟨a, fixedModule_anti T.le a.2⟩).1 a.2⟩
  invFun m := ⟨T.equiv.symm m, (T.mem_fixedModule_iff _).2 (by simp [m.2])⟩
  left_inv a := by simp
  right_inv m := by simp
  map_mul' a b := by
    ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul]
    rfl

@[simp]
theorem coe_fixedModuleEquiv (a : fixedModule A K) :
    (T.fixedModuleEquiv a : M) = T.equiv ⟨a, fixedModule_anti T.le a.2⟩ :=
  rfl

variable [(L.subgroupOf K).Normal]

noncomputable def quotientEquiv : K ⧸ L.subgroupOf K ≃* Γ :=
  (QuotientGroup.quotientMulEquivOfEq T.ker_hom.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective T.hom T.surjective_hom)


include T in
theorem relIndex_eq_natCard : L.relIndex K = Nat.card Γ :=
  Nat.card_congr T.quotientEquiv.toEquiv

theorem exists_cosetSMul (a : fixedModule A L) (q : K ⧸ L.subgroupOf K) :
    ∃ h : cosetSMul A K L a q ∈ fixedModule A L,
      T.equiv ⟨cosetSMul A K L a q, h⟩ = T.quotientEquiv q • T.equiv a := by
  induction q using QuotientGroup.induction_on with
  | H σ =>
    have h := smul_mem_fixedModule_of_normal T.le σ.2 a.2
    exact ⟨h, T.equiv_smul σ a h⟩

theorem norm_eq [Fintype Γ] [(L.subgroupOf K).FiniteIndex] (a : fixedModule A L) :
    T.equiv ⟨norm A K L a, fixedModule_anti T.le (norm A K L a).2⟩ = tateNorm Γ M (T.equiv a) := by
  classical
  let _ := Fintype.ofFinite (K ⧸ L.subgroupOf K)
  choose hmem hval using T.exists_cosetSMul a
  have hprod : (⟨norm A K L a, fixedModule_anti T.le (norm A K L a).2⟩ : fixedModule A L) =
      ∏ q, (⟨cosetSMul A K L a q, hmem q⟩ : fixedModule A L) := by
    ext
    rw [coe_norm, finprod_eq_prod_of_fintype, Subgroup.val_finsetProd]
  rw [hprod, map_prod, GroundTheory.LocalField.tateNorm_apply]
  simp_rw [hval]
  exact Fintype.prod_equiv T.quotientEquiv.toEquiv _ _ fun _ => rfl

theorem map_range_norm [Fintype Γ] [(L.subgroupOf K).FiniteIndex] :
    (norm A K L).range.map T.fixedModuleEquiv.toMonoidHom =
      (tateNorm Γ M).range.subgroupOf (invariants Γ M) := by
  ext m
  simp only [Subgroup.mem_map, MonoidHom.mem_range, MulEquiv.coe_toMonoidHom,
    Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨T.equiv a, by rw [coe_fixedModuleEquiv, T.norm_eq]⟩
  · rintro ⟨x, hx⟩
    refine ⟨_, ⟨T.equiv.symm x, rfl⟩, Subtype.ext ?_⟩
    rw [coe_fixedModuleEquiv, T.norm_eq, MulEquiv.apply_symm_apply, hx]

noncomputable def tateZeroEquiv [Fintype Γ] [(L.subgroupOf K).FiniteIndex] :
    tateZero A K L ≃* TateZero Γ M :=
  QuotientGroup.congr _ _ T.fixedModuleEquiv T.map_range_norm

include T in
theorem natCard_tateZero [Fintype Γ] [(L.subgroupOf K).FiniteIndex] :
    Nat.card (tateZero A K L) = Nat.card (TateZero Γ M) :=
  Nat.card_congr T.tateZeroEquiv.toEquiv

theorem norm_eq_one_iff [Fintype Γ] [(L.subgroupOf K).FiniteIndex] (a : fixedModule A L) :
    norm A K L a = 1 ↔ tateNorm Γ M (T.equiv a) = 1 := by
  rw [← T.norm_eq, MulEquiv.map_eq_one_iff]
  constructor
  · intro h
    ext
    simp [h]
  · intro h
    exact Subtype.ext (by simpa using congrArg Subtype.val h)

theorem map_ker_norm [Fintype Γ] [(L.subgroupOf K).FiniteIndex] :
    (norm A K L).ker.map T.equiv.toMonoidHom = (tateNorm Γ M).ker := by
  ext m
  simp only [Subgroup.mem_map, MonoidHom.mem_ker, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (T.norm_eq_one_iff a).1 ha
  · intro hm
    exact ⟨T.equiv.symm m, (T.norm_eq_one_iff _).2 (by simpa using hm), by simp⟩


omit [(L.subgroupOf K).Normal] in
theorem augmentation_eq_map :
    augmentation A K L =
      (GroundTheory.LocalField.augmentation Γ M).map
        ((fixedModule A L).subtype.comp T.equiv.symm.toMonoidHom) := by
  rw [augmentation, GroundTheory.LocalField.augmentation, MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image, MonoidHom.coe_comp, Subgroup.coe_subtype,
    MulEquiv.coe_toMonoidHom, Function.comp_apply]
  constructor
  · rintro ⟨g, hg, a, ha, rfl⟩
    refine ⟨T.hom ⟨g, hg⟩ • T.equiv ⟨a, ha⟩ / T.equiv ⟨a, ha⟩, ⟨_, _, rfl⟩, ?_⟩
    rw [map_div, Subgroup.coe_div, T.coe_equiv_symm_smul, MulEquiv.symm_apply_apply]
  · rintro ⟨_, ⟨γ, m, rfl⟩, rfl⟩
    obtain ⟨σ, rfl⟩ := T.surjective_hom γ
    refine ⟨σ, σ.2, T.equiv.symm m, (T.equiv.symm m).2, ?_⟩
    have h := T.coe_equiv_symm_smul σ (T.equiv.symm m)
    rw [MulEquiv.apply_symm_apply] at h
    rw [map_div, Subgroup.coe_div, h]


omit [(L.subgroupOf K).Normal] in
theorem mem_augmentation_iff (a : fixedModule A L) :
    (a : A) ∈ augmentation A K L ↔ T.equiv a ∈ GroundTheory.LocalField.augmentation Γ M := by
  rw [T.augmentation_eq_map]
  constructor
  · rintro ⟨m, hm, h⟩
    have : T.equiv.symm m = a := Subtype.ext h
    rw [← this, MulEquiv.apply_symm_apply]
    exact hm
  · intro h
    exact ⟨T.equiv a, h, by simp⟩

noncomputable def kerEquiv [Fintype Γ] [(L.subgroupOf K).FiniteIndex] :
    (norm A K L).ker ≃* (tateNorm Γ M).ker :=
  (T.equiv.subgroupMap (norm A K L).ker).trans (MulEquiv.subgroupCongr T.map_ker_norm)

@[simp]
theorem coe_kerEquiv [Fintype Γ] [(L.subgroupOf K).FiniteIndex] (a : (norm A K L).ker) :
    (T.kerEquiv a : M) = T.equiv a :=
  rfl

noncomputable def tateNegOneEquiv [Fintype Γ] [(L.subgroupOf K).FiniteIndex] :
    tateNegOne A K L ≃* TateNegOne Γ M :=
  QuotientGroup.congr _ _ T.kerEquiv <| by
    ext m
    obtain ⟨a, rfl⟩ := T.kerEquiv.surjective m
    simp only [Subgroup.mem_map, Subgroup.mem_comap, Subgroup.mem_subgroupOf, MonoidHom.coe_comp,
      Subgroup.coe_subtype, Function.comp_apply, coe_kerEquiv]
    constructor
    · rintro ⟨x, hx, hxa⟩
      rw [T.kerEquiv.injective hxa] at hx
      exact (T.mem_augmentation_iff _).1 hx
    · intro h
      exact ⟨a, (T.mem_augmentation_iff _).2 h, rfl⟩

include T in
theorem natCard_tateNegOne [Fintype Γ] [(L.subgroupOf K).FiniteIndex] :
    Nat.card (tateNegOne A K L) = Nat.card (TateNegOne Γ M) :=
  Nat.card_congr T.tateNegOneEquiv.toEquiv

end TateModel

end Model

end GroundTheory.LocalField.Abstract
end

section

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel

class IsUnramified (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L] [ValuativeExtension K L] : Prop where

  ramificationIndex_eq_one : (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) = 1

section Algebraic

variable (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]

theorem isUnramified_iff : IsUnramified K L ↔ (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) = 1 :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩

end Algebraic

section Topological

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem isUnramified_iff_residueDegree_eq_finrank :
    IsUnramified K L ↔ ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) = Module.finrank K L := by
  rw [isUnramified_iff, ← ramificationIndex_mul_residueDegree K L]
  change ramificationIndex K L = 1 ↔ _
  have h := residueDegree_pos K L
  constructor
  · intro h1
    rw [h1, one_mul]
  · intro h1
    have : (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) * ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) = 1 * ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) := by
      rw [one_mul]
      exact h1.symm
    exact Nat.eq_of_mul_eq_mul_right h this

theorem isUnramified_iff_finrank_residueField :
    IsUnramified K L ↔ Module.finrank 𝓀[K] 𝓀[L] = Module.finrank K L := by
  rw [isUnramified_iff_residueDegree_eq_finrank, residueDegree_eq_finrank]

theorem IsUnramified.residueDegree_eq_finrank [IsUnramified K L] :
    ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) = Module.finrank K L :=
  (isUnramified_iff_residueDegree_eq_finrank K L).1 inferInstance

theorem IsUnramified.finrank_residueField [IsUnramified K L] :
    Module.finrank 𝓀[K] 𝓀[L] = Module.finrank K L :=
  (isUnramified_iff_finrank_residueField K L).1 inferInstance

end Topological

section Tower

variable (K L M : Type*) [Field K] [ValuativeRel K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [ValuativeExtension K L] [ValuativeExtension L M] [ValuativeExtension K M]
  [FiniteDimensional L M]

theorem isUnramified_tower_iff :
    IsUnramified K M ↔ IsUnramified K L ∧ IsUnramified L M := by
  simp only [isUnramified_iff, ramificationIndex_tower K L M, mul_eq_one]

end Tower

end GroundTheory.LocalField
end
end
