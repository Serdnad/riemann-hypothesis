module

public import GroundTheory.GlobalFields.NormResidueSymbol.RangeIdeleNormLeKerIdeleSymbol
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.Bundle005
public import GroundTheory.GlobalFields.NormResidueSymbol.CyclotomicCompositum
public import GroundTheory.GlobalFields.NormResidueSymbol.RationalDiagonal
import GroundTheory.GlobalFields.NormResidueSymbol.Bundle002
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.Bundle006
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
import Mathlib.Tactic.PNatToNat

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain IdeleGroup

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

attribute [local instance] FiniteSubfield.isGalois_of_normal

theorem sup_rootsOfUnityField_mono (F : IntermediateField ℚ ℚ̄) {m n : ℕ} (h : m ∣ n) :
    F ⊔ Cyclotomic.rootsOfUnityField m ≤ F ⊔ Cyclotomic.rootsOfUnityField n := by
  refine sup_le_sup_left (IntermediateField.adjoin.mono ℚ _ _ fun x hx ↦ ?_) F
  obtain ⟨c, rfl⟩ := h
  change x ^ (m * c) = 1
  rw [pow_mul, show x ^ m = 1 from hx, one_pow]

theorem exists_le_sup_rootsOfUnityField (F E : IntermediateField ℚ ℚ̄) [FiniteDimensional ℚ E]
    (hE : E ≤ F ⊔ Cyclotomic.maxCyclotomic) :
    ∃ n : ℕ+, E ≤ F ⊔ Cyclotomic.rootsOfUnityField n := by
  set T : ℕ+ → IntermediateField ℚ ℚ̄ := fun n ↦ F ⊔ Cyclotomic.rootsOfUnityField n with hT
  have hdir : Directed (· ≤ ·) T := fun m n ↦
    ⟨m * n, sup_rootsOfUnityField_mono F (by simp), sup_rootsOfUnityField_mono F (by simp)⟩
  have hsup : F ⊔ Cyclotomic.maxCyclotomic = ⨆ n, T n := by
    rw [Cyclotomic.maxCyclotomic_eq_iSup, sup_iSup]
  set b := Module.finBasis ℚ E with hb
  have hmem : ∀ i, ∃ n, ((b i : E) : ℚ̄) ∈ T n := fun i ↦ by
    have h := hE (b i).2
    rw [hsup, ← SetLike.mem_coe, coe_iSup_of_directed hdir, Set.mem_iUnion] at h
    exact h
  choose n hn using hmem
  obtain ⟨z, hz⟩ := hdir.finset_le (Finset.univ.image n)
  refine ⟨z, fun x hx ↦ ?_⟩
  have hbT : ∀ i, ((b i : E) : ℚ̄) ∈ T z := fun i ↦
    hz (n i) (Finset.mem_image_of_mem n (Finset.mem_univ i)) (hn i)
  have hx' : (⟨x, hx⟩ : E) ∈ Submodule.span ℚ (Set.range b) := b.mem_span _
  have hmap := Submodule.mem_map_of_mem (f := E.val.toLinearMap) hx'
  rw [Submodule.map_span, ← Set.range_comp] at hmap
  exact (Submodule.span_le (p := (T z).toSubalgebra.toSubmodule)).2
    (by rintro _ ⟨i, rfl⟩; exact hbT i) hmap

variable {K : FiniteSubfield} (E : FiniteSubfield) [Fact (K ≤ E)]
  [(E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal] [IsMulCommutative (E.1 ≃ₐ[K.1] E.1)]

theorem ideleSymbol_diagonal_eq_one_of_le_sup_maxCyclotomic (hE : E.1 ≤ K.1 ⊔ Cyclotomic.maxCyclotomic)
    (a : K.1ˣ) : ideleSymbol K.1 E.1 (diagonal K.1 a) = 1 := by
  obtain ⟨n, hn⟩ := exists_le_sup_rootsOfUnityField K.1 E.1 hE
  have : FiniteDimensional ℚ (Cyclotomic.rootsOfUnityField n) :=
    IsCyclotomicExtension.finiteDimensional {(n : ℕ)} ℚ _
  set F : FiniteSubfield := ⟨Cyclotomic.rootsOfUnityField n, inferInstance⟩ with hF
  have : IsCyclotomicExtension {(n : ℕ)} ℚ F.1 :=
    (inferInstance : IsCyclotomicExtension {(n : ℕ)} ℚ (Cyclotomic.rootsOfUnityField n))
  have : IsGalois ℚ F.1 := IsCyclotomicExtension.isGalois {(n : ℕ)} ℚ F.1
  have : IsMulCommutative (F.1 ≃ₐ[ℚ] F.1) := IsCyclotomicExtension.isMulCommutative {(n : ℕ)} ℚ F.1
  set M := CyclotomicSymbol.compositum K F with hM
  have : Fact (E ≤ M) := ⟨hn⟩
  have : IsScalarTower K.1 E.1 M.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hMone : ideleSymbol K.1 M.1 (diagonal K.1 a) = 1 := by
    have h := CyclotomicSymbol.restrictHom_eq_ideleSymbol K F 1 (diagonal K.1 a) (by
      rw [ideleNorm_diagonal, RationalSymbol.ideleSymbol_diagonal_eq_one F.1 {(n : ℕ)}]
      exact map_one (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := ℚ̄) F.1))
    rw [← h, map_one]
  rw [← restrictNormal_ideleSymbol E.1 M.1, hMone]
  exact map_one (AlgEquiv.restrictNormalHom (F := K.1) (K₁ := M.1) E.1)

variable (ι : LocalEmbeddings K)

theorem finsum_char_localSymbolAt_eq_zero (hE : E.1 ≤ K.1 ⊔ Cyclotomic.maxCyclotomic)
    (χ : Additive K.1.fixingSubgroup →ₜ+ QZ)
    (hχ : ∀ h : K.1.fixingSubgroup, (h : ℚ̄ ≃ₐ[ℚ] ℚ̄) ∈ E.1.fixingSubgroup → χ (Additive.ofMul h) = 0)
    (a : K.1ˣ) :
    ∑ᶠ v : Place K.1, χ (Additive.ofMul (localSymbolAt ι v a)) = 0 := by
  rw [finsum_char_localSymbolAt_eq ι E χ hχ a 1
    (by rw [map_one, ideleSymbol_diagonal_eq_one_of_le_sup_maxCyclotomic E hE a]), ofMul_one, map_zero]

end

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield}

def openSubgroupMap (U : OpenSubgroup K.1.fixingSubgroup) : OpenSubgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄) :=
  ⟨(U : Subgroup K.1.fixingSubgroup).map K.1.fixingSubgroup.subtype, by
    have hK : IsOpen (K.1.fixingSubgroup : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄)) := K.1.fixingSubgroup_isOpen
    have := hK.isOpenMap_subtype_val _ U.isOpen
    convert this using 1
    ext x
    simp⟩

def fieldOf (U : OpenSubgroup K.1.fixingSubgroup) : FiniteSubfield :=
  ofOpenSubgroup (openSubgroupMap U)

theorem fixingSubgroup_fieldOf (U : OpenSubgroup K.1.fixingSubgroup) :
    (fieldOf U).1.fixingSubgroup = (U : Subgroup K.1.fixingSubgroup).map K.1.fixingSubgroup.subtype :=
  fixingSubgroup_ofOpenSubgroup (openSubgroupMap U)

theorem fixingSubgroup_fieldOf_le (U : OpenSubgroup K.1.fixingSubgroup) :
    (fieldOf U).1.fixingSubgroup ≤ K.1.fixingSubgroup := by
  rw [fixingSubgroup_fieldOf]
  rintro _ ⟨g, _, rfl⟩
  exact g.2

theorem subgroupOf_fieldOf (U : OpenSubgroup K.1.fixingSubgroup) :
    (fieldOf U).1.fixingSubgroup.subgroupOf K.1.fixingSubgroup = U := by
  rw [fixingSubgroup_fieldOf, Subgroup.subgroupOf]
  exact Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _

theorem fieldOf_le_fieldOf {U V : OpenSubgroup K.1.fixingSubgroup} (h : V ≤ U) : fieldOf U ≤ fieldOf V := by
  have hle : (fieldOf V).1.fixingSubgroup ≤ (fieldOf U).1.fixingSubgroup := by
    rw [fixingSubgroup_fieldOf, fixingSubgroup_fieldOf]
    exact Subgroup.map_mono h
  have h' := IntermediateField.fixedField_antitone hle
  rwa [InfiniteGalois.fixedField_fixingSubgroup, InfiniteGalois.fixedField_fixingSubgroup] at h'

def openEquiv (U : OpenSubgroup K.1.fixingSubgroup) : (U : Subgroup K.1.fixingSubgroup) ≃* (fieldOf U).1.fixingSubgroup :=
  (MulEquiv.subgroupCongr (subgroupOf_fieldOf U).symm).trans
    (Subgroup.subgroupOfEquivOfLe (fixingSubgroup_fieldOf_le U))

theorem continuous_openEquiv (U : OpenSubgroup K.1.fixingSubgroup) : Continuous (openEquiv U).toMonoidHom :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem continuous_openEquiv_symm (U : OpenSubgroup K.1.fixingSubgroup) :
    Continuous (openEquiv U).symm.toMonoidHom :=
  (continuous_subtype_val.subtype_mk _).subtype_mk _

def classOpenMor (U : OpenSubgroup K.1.fixingSubgroup) :
    Rep.res (openEquiv U).symm.toMonoidHom (Rep.res (U : Subgroup K.1.fixingSubgroup).subtype (classLimitRep K)) ⟶
      classLimitRep (fieldOf U) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

def classOpenIso (U : OpenSubgroup K.1.fixingSubgroup) (n : ℕ) :
    cohomology (Rep.res (U : Subgroup K.1.fixingSubgroup).subtype (classLimitRep K)) n ≅
      cohomology (classLimitRep (fieldOf U)) n :=
  haveI := isIso_cohomologyMapAlong_of_mulEquiv (openEquiv U).symm (continuous_openEquiv_symm U)
    (continuous_openEquiv U) (classOpenMor U) Function.bijective_id n
  asIso (cohomologyMapAlong (openEquiv U).symm.toMonoidHom (continuous_openEquiv_symm U) (classOpenMor U) n)

theorem cohomologyResLE_classOpenIso {U V : OpenSubgroup K.1.fixingSubgroup} (h : V ≤ U) (n : ℕ) :
    haveI : Fact (fieldOf U ≤ fieldOf V) := ⟨fieldOf_le_fieldOf h⟩
    cohomologyResLE (classLimitRep K) (show (V : Subgroup K.1.fixingSubgroup) ≤ U from h) n ≫
        (classOpenIso V n).hom =
      (classOpenIso U n).hom ≫ classResField (fieldOf U) (fieldOf V) n := by
  have : Fact (fieldOf U ≤ fieldOf V) := ⟨fieldOf_le_fieldOf h⟩
  rw [classOpenIso, classOpenIso, asIso_hom, asIso_hom, cohomologyResLE, classResField,
    ← cohomologyMapAlong_comp, ← cohomologyMapAlong_comp]
  exact cohomologyMapAlong_congr _ _ _ _ (MonoidHom.ext fun g => Subtype.ext (Subtype.ext rfl)) (fun _ => rfl) n

theorem relIndex_eq_finrank_fieldOf {U V : OpenSubgroup K.1.fixingSubgroup} (h : V ≤ U) :
    letI := algebraOfLE (fieldOf_le_fieldOf h)
    (V : Subgroup K.1.fixingSubgroup).relIndex U = Module.finrank (fieldOf U).1 (fieldOf V).1 := by
  have := relIndex_fixingSubgroup (fieldOf_le_fieldOf h)
  rw [fixingSubgroup_fieldOf, fixingSubgroup_fieldOf,
    Subgroup.relIndex_map_map_of_injective _ _ Subtype.val_injective] at this
  exact this

end

end GroundTheory.ProfCoh
end
