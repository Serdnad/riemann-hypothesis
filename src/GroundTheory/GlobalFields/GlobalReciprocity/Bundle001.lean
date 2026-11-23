module

public import GroundTheory.GlobalFields.GlobalReciprocity.InfKerDegreeLeOfLeSupZhatField
public import GroundTheory.GlobalFields.NormResidueSymbol.Functorial
public import GroundTheory.GlobalFields.NormResidueSymbol.Cyclotomic
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
import Mathlib.GroupTheory.Abelianization.Finite
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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

open NumberField IntermediateField GroundTheory.LocalField.Abstract IdeleGroup
open scoped GroundTheory.LocalField.Abstract

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem eq_of_ker_le_of_natCard_le_two {A B : Type*} [Group A] [Group B] [Finite B]
    (hB : Nat.card B ≤ 2) {f g : A →* B} (hfg : f.ker ≤ g.ker) {y : A} (hy : g y ≠ 1) : f = g := by
  classical
  have key : ∀ b b' : B, b ≠ 1 → b' ≠ 1 → b = b' := by
    intro b b' hb hb'
    by_contra hne
    have : Fintype B := Fintype.ofFinite B
    have h3 : ({1, b, b'} : Finset B).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair hne]
      simp [Ne.symm hb, Ne.symm hb']
    have h4 := Finset.card_le_univ ({1, b, b'} : Finset B)
    rw [Nat.card_eq_fintype_card] at hB
    omega
  have hfy : f y ≠ 1 := fun h ↦ hy (hfg h)
  ext x
  by_cases hx : f x = 1
  · rw [hx]
    exact (hfg hx).symm
  · have e : x * y⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, key _ _ hx hfy, mul_inv_cancel]
    have e' : g x = g y := by
      have h := hfg e
      rwa [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at h
    exact key _ _ hx (e' ▸ hy)

theorem abelianization_of_injective {Γ : Type*} [Group Γ] [IsMulCommutative Γ] :
    Function.Injective (Group.Abelianization.of : Γ →* Group.Abelianization Γ) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h : g ∈ commutator Γ := by
    rw [← Group.Abelianization.ker_of]
    exact hg
  rw [commutator, Subgroup.commutator_eq_bot_iff_le_centralizer.2
    (fun x _ y _ ↦ mul_comm' y x)] at h
  exact h

namespace IdeleClassLimit

open FiniteSubfield RationalSymbol CyclotomicSymbol _root_.GroundTheory.Global.Cyclotomic

variable (K L : FiniteSubfield) [hKL : Fact (K ≤ L)]
  [(L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal]

theorem exists_eq_ideleClassNorm_of_abstractSymbol_eq_one {c : IdeleClassGroup K.1}
    (h : abstractSymbol K L c = 1) : ∃ d : IdeleClassGroup L.1, FiniteSubfield.ideleClassNorm hKL.out d = c := by
  set e := quotientGaloisEquiv K L
  have key : (Group.Abelianization.map e.symm.toMonoidHom).comp (Group.Abelianization.map e.toMonoidHom) =
      MonoidHom.id _ := by
    refine Group.Abelianization.hom_ext _ _ (MonoidHom.ext fun q ↦ ?_)
    simp
  have hinj : Function.Injective (Group.Abelianization.map e.toMonoidHom) := fun a b hab ↦ by
    have := congrArg (Group.Abelianization.map e.symm.toMonoidHom) hab
    rwa [← MonoidHom.comp_apply, ← MonoidHom.comp_apply, key] at this
  rw [abstractSymbol_apply, ← map_one (Group.Abelianization.map e.toMonoidHom)] at h
  have h1 := hinj h
  rw [MulEquiv.symm_apply_eq, map_one] at h1
  have h2 : fixedEquiv K c ∈ (norm IdeleClassLimit (K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))
      (L.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))).range := by
    rw [normClass, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  obtain ⟨b, hb⟩ := h2
  refine ⟨(fixedEquiv L).symm b, (fixedEquiv K).injective ?_⟩
  rw [← norm_fixedEquiv hKL.out, MulEquiv.apply_symm_apply]
  exact hb

variable [IsMulCommutative (L.1 ≃ₐ[K.1] L.1)]

theorem ideleSymbol_eq_one_of_abstractSymbol_eq_one (hL : L.1 ≤ K.1 ⊔ maxCyclotomic)
    {x : IdeleGroup K.1} (h : abstractSymbol K L (IdeleClassGroup.mk K.1 x) = 1) :
    ideleSymbol K.1 L.1 x = 1 := by
  obtain ⟨d, hd⟩ := exists_eq_ideleClassNorm_of_abstractSymbol_eq_one K L h
  obtain ⟨y, rfl⟩ := IdeleClassGroup.mk_surjective L.1 d
  have hd' : (QuotientGroup.mk (ideleNorm K.1 L.1 y) : IdeleClassGroup K.1) = QuotientGroup.mk x :=
    hd
  obtain ⟨a, ha⟩ := QuotientGroup.eq.1 hd'
  have hx : x = ideleNorm K.1 L.1 y * diagonal K.1 a := by
    rw [ha, mul_inv_cancel_left]
  rw [hx, map_mul, ideleSymbol_ideleNorm, ideleSymbol_diagonal_eq_one_of_le_sup K L hL, mul_one]

theorem abstractSymbol_mk_of_natCard_le_two (hcard : Nat.card (L.1 ≃ₐ[K.1] L.1) ≤ 2)
    (hL : L.1 ≤ K.1 ⊔ maxCyclotomic) {y : IdeleGroup K.1} (hy : ideleSymbol K.1 L.1 y ≠ 1)
    (x : IdeleGroup K.1) :
    abstractSymbol K L (IdeleClassGroup.mk K.1 x) = Group.Abelianization.of (ideleSymbol K.1 L.1 x) := by
  have hB : Nat.card (Group.Abelianization (L.1 ≃ₐ[K.1] L.1)) ≤ 2 :=
    (Nat.card_le_card_of_surjective _ (QuotientGroup.mk_surjective (s := commutator _))).trans hcard
  have h := eq_of_ker_le_of_natCard_le_two hB
    (f := (abstractSymbol K L).comp (IdeleClassGroup.mk K.1))
    (g := Group.Abelianization.of.comp (ideleSymbol K.1 L.1)) (y := y)
    (fun z hz ↦ by
      change abstractSymbol K L (IdeleClassGroup.mk K.1 z) = 1 at hz
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        ideleSymbol_eq_one_of_abstractSymbol_eq_one K L hL hz, map_one])
    (fun h1 ↦ hy (abelianization_of_injective (by rw [MonoidHom.comp_apply] at h1; rw [h1, map_one])))
  exact congrArg (fun f : IdeleGroup K.1 →* Group.Abelianization (L.1 ≃ₐ[K.1] L.1) ↦ f x) h

end IdeleClassLimit

end

end GroundTheory.Global
end

section

namespace GroundTheory.Global

open NumberField IntermediateField GroundTheory.LocalField.Abstract IdeleGroup
open scoped GroundTheory.LocalField.Abstract

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ

namespace IdeleClassLimit

open FiniteSubfield RationalSymbol CyclotomicSymbol _root_.GroundTheory.Global.Cyclotomic ProfiniteInteger

theorem val_norm_fixedEquiv (K : FiniteSubfield) (a : IdeleClassGroup K.1) :
    val (norm IdeleClassLimit ⊤ K.1.fixingSubgroup (fixedEquiv K a)) = cycDegree (cycSymbol K a) := by
  have h := val_norm_of (U := K.1.fixingSubgroup) rfl a (fixedEquiv K a).2
  convert h using 3
  exact Subtype.ext (coe_fixedEquiv K a)

theorem degree_eq_valuation_pow (K : FiniteSubfield) (a : IdeleClassGroup K.1) {g : ℚ̄ ≃ₐ[ℚ] ℚ̄}
    (hg : cycRestrict g = cycSymbol K a) :
    classFieldTheory.deg g =
      classFieldTheory.valuation K.openSubgroup (fixedEquiv K a) ^
        inertiaDegree classFieldTheory.deg (K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) := by
  have h3 : degree g = cycDegree (cycSymbol K a) := by
    rw [← hg, ← MonoidHom.comp_apply, cycDegree_comp_cycRestrict]
  rw [classFieldTheory.valuation_pow K.openSubgroup (fixedEquiv K a)]
  convert h3.trans (val_norm_fixedEquiv K a).symm using 2
  · exact classFieldTheory_deg
  · rfl

variable (K L : FiniteSubfield) [hKL : Fact (K ≤ L)]
  [(L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal]

theorem abstractSymbol_eq_of_cycRestrict_eq (hL : L.1 ≤ K.1 ⊔ zhatField) (a : IdeleClassGroup K.1)
    (g : K.1.fixingSubgroup) (hg : cycRestrict (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) = cycSymbol K a) :
    abstractSymbol K L a = Group.Abelianization.of (restrictHom g) := by
  set D := classFieldTheory.toClassFieldData
  have hLK : L.openSubgroup ≤ K.openSubgroup := openSubgroup_le hKL.out
  have hu : (K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) ⊓ D.deg.ker ≤ L.openSubgroup :=
    inf_ker_degree_le_of_le_sup_zhatField K L hL
  obtain ⟨φ, hφ⟩ := D.relDeg_surjective K.openSubgroup (Multiplicative.ofAdd 1)
  have hr := D.reciprocityAbEquiv_symm_of_unramified hLK classFieldTheory.classFieldAxiom hu hφ
    (fixedEquiv K a)
  set f := D.relInertiaDegreePNat hLK with hf
  set z := Multiplicative.toAdd (D.valuation K.openSubgroup (fixedEquiv K a)) with hz
  set n := (proj f z).val with hn

  obtain ⟨y, hy⟩ : ∃ y : ℤ̂, z - (n : ℤ̂) = (f : ℕ) • y := by
    refine exists_eq_nsmul_of_proj_eq_zero ?_
    rw [map_sub, map_natCast, hn, ZMod.natCast_zmod_val, sub_self]

  have hmem : ((φ ^ n)⁻¹ * g : (K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))) ∈
      (L.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)).subgroupOf K.openSubgroup := by
    rw [Subgroup.mem_subgroupOf, mem_iff_map_mem_of_unramified (d := D.deg) hLK hu
      ((φ ^ n)⁻¹ * g : (K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))).2,
      D.mem_map_deg_iff L.openSubgroup]
    refine ⟨Multiplicative.ofAdd y, ?_⟩
    have hφd : D.deg φ = Multiplicative.ofAdd 1 ^ inertiaDegree D.deg
        (K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) := by
      rw [← D.relDeg_pow K.openSubgroup φ, hφ]
    have hgd : D.deg g = D.valuation K.openSubgroup (fixedEquiv K a) ^
        inertiaDegree D.deg (K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) :=
      degree_eq_valuation_pow K a hg
    rw [inertiaDegree_eq_mul D.surjective_deg hLK]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_pow, map_mul, map_inv, map_pow]
    rw [hφd, show D.deg (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) = _ from hgd]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_pow, toAdd_mul, toAdd_inv, toAdd_ofAdd]
    change _ = _ + _ • z
    rw [sub_eq_iff_eq_add'.1 hy, hf, ClassFieldData.coe_relInertiaDegreePNat]
    simp only [nsmul_eq_mul, Nat.cast_mul]
    ring
  have e : (reciprocityEquiv K L).symm (normClass K L a) =
      Group.Abelianization.of (QuotientGroup.mk (s := (L.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)).subgroupOf
        K.openSubgroup) g) := by
    refine hr.trans ?_
    rw [← map_pow, ← QuotientGroup.mk_pow]
    exact congrArg _ (QuotientGroup.eq.2 hmem)
  rw [abstractSymbol_apply, e, Group.Abelianization.map_of]
  rfl

theorem abstractSymbol_mk_of_le_sup_zhatField [IsMulCommutative (L.1 ≃ₐ[K.1] L.1)]
    (hL : L.1 ≤ K.1 ⊔ zhatField) (x : IdeleGroup K.1) :
    abstractSymbol K L (IdeleClassGroup.mk K.1 x) =
      Group.Abelianization.of (ideleSymbol K.1 L.1 x) := by
  obtain ⟨g, hgK, hg⟩ := exists_mem_fixingSubgroup_cycRestrict_eq K (IdeleClassGroup.mk K.1 x)
  rw [abstractSymbol_eq_of_cycRestrict_eq K L hL _ ⟨g, hgK⟩ hg,
    restrictHom_eq_ideleSymbol_of_le_sup K L (hL.trans (sup_le_sup_left zhatField_le_maxCyclotomic _))
      ⟨g, hgK⟩ x hg]

end IdeleClassLimit

end

end GroundTheory.Global
end

section

namespace GroundTheory.Global

open NumberField IntermediateField GroundTheory.LocalField.Abstract
open scoped GroundTheory.LocalField.Abstract

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ

namespace IdeleClassLimit

open FiniteSubfield

section Kernel

variable (K L : FiniteSubfield) [hKL : Fact (K ≤ L)]
  [(L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal]


omit [(L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal] in
theorem normClass_ideleClassNorm (c : IdeleClassGroup L.1) :
    normClass K L (FiniteSubfield.ideleClassNorm hKL.out c) = 1 := by
  change (QuotientGroup.mk (fixedEquiv K (FiniteSubfield.ideleClassNorm hKL.out c)) :
    tateZero IdeleClassLimit (K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) L.openSubgroup) = 1
  rw [QuotientGroup.eq_one_iff, ← norm_fixedEquiv hKL.out c]
  exact ⟨_, rfl⟩

theorem abstractSymbol_ideleClassNorm_eq_one (c : IdeleClassGroup L.1) :
    abstractSymbol K L (FiniteSubfield.ideleClassNorm hKL.out c) = 1 := by
  rw [abstractSymbol_apply, normClass_ideleClassNorm, map_one, map_one]

theorem exists_abstractSymbol_eq (c : IdeleClassGroup K.1) :
    ∃ g : K.1.fixingSubgroup, abstractSymbol K L c = Group.Abelianization.of (restrictHom g) := by
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (abstractSymbol K L c)
  obtain ⟨g, rfl⟩ := restrictHom_surjective (F := K) (E := L) σ
  exact ⟨g, hσ.symm⟩

end Kernel

section Square

variable {K L K' L' : FiniteSubfield} [hKL : Fact (K ≤ L)]
  [(L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal] [hKL' : Fact (K' ≤ L')]
  [(L'.1.fixingSubgroup.subgroupOf K'.1.fixingSubgroup).Normal]


omit [(L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal]
  [(L'.1.fixingSubgroup.subgroupOf K'.1.fixingSubgroup).Normal] in
theorem normTateZero_normClass (hK : K ≤ K') (hL : L ≤ L') (c : IdeleClassGroup K'.1) :
    normTateZero (openSubgroup_le hK) (openSubgroup_le hL) (openSubgroup_le hKL'.out)
        (openSubgroup_le hKL.out) (normClass K' L' c) =
      normClass K L (FiniteSubfield.ideleClassNorm hK c) := by
  change normTateZero (openSubgroup_le hK) (openSubgroup_le hL) (openSubgroup_le hKL'.out)
      (openSubgroup_le hKL.out) (QuotientGroup.mk (fixedEquiv K' c)) =
    QuotientGroup.mk (fixedEquiv K (FiniteSubfield.ideleClassNorm hK c))
  rw [normTateZero_mk]
  exact congrArg _ (norm_fixedEquiv hK c)

theorem abstractSymbol_ideleClassNorm (hK : K ≤ K') (hL : L ≤ L') (c : IdeleClassGroup K'.1)
    (g : K'.1.fixingSubgroup) (hg : abstractSymbol K' L' c = Group.Abelianization.of (restrictHom g)) :
    abstractSymbol K L (FiniteSubfield.ideleClassNorm hK c) =
      Group.Abelianization.of (restrictHom (⟨g, IntermediateField.fixingSubgroup_le
        (show K.1 ≤ K'.1 from hK) g.2⟩ : K.1.fixingSubgroup)) := by
  set D := classFieldTheory.toClassFieldData
  have e : (reciprocityEquiv K' L').symm (normClass K' L' c) =
      Group.Abelianization.of (QuotientGroup.mk (s := (L'.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)).subgroupOf
        K'.openSubgroup) g) := by
    apply (quotientGaloisEquiv K' L').abelianizationCongr.injective
    rw [Group.abelianizationCongr_of, quotientGaloisEquiv_mk]
    exact hg
  rw [abstractSymbol_apply, ← normTateZero_normClass hK hL c]
  have h2 := D.reciprocityAbEquiv_symm_normTateZero classFieldTheory.classFieldAxiom
    (openSubgroup_le hKL.out) (openSubgroup_le hKL'.out) (openSubgroup_le hK) (openSubgroup_le hL)
    (normClass K' L' c)
  rw [h2, e, Group.Abelianization.map_of, Group.Abelianization.map_of, galRestrict_mk]
  rfl

instance isScalarTower_of_fact {F E M : FiniteSubfield} [Fact (F ≤ E)] [Fact (E ≤ M)] [Fact (F ≤ M)] :
    IsScalarTower F.1 E.1 M.1 :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

theorem abstractSymbol_ideleClassNorm_eq_map [hK : Fact (K ≤ K')] [Fact (L ≤ L')] [Fact (K ≤ L')]
    (c : IdeleClassGroup K'.1) :
    abstractSymbol K L (FiniteSubfield.ideleClassNorm hK.out c) =
      Group.Abelianization.map ((AlgEquiv.restrictNormalHom (F := K.1) (K₁ := L'.1) L.1).comp
        (restrictScalarsHom (L' := L'.1) K.1)) (abstractSymbol K' L' c) := by
  obtain ⟨g, hg⟩ := exists_abstractSymbol_eq K' L' c
  rw [abstractSymbol_ideleClassNorm hK.out (Fact.out : L ≤ L') c g hg, hg, Group.Abelianization.map_of]
  congr 1
  refine AlgEquiv.ext fun x ↦ Subtype.ext ?_
  have h := congrArg (fun z : L'.1 ↦ (z : ℚ̄))
    (AlgEquiv.restrictNormal_commutes ((restrictHom g : L'.1 ≃ₐ[K'.1] L'.1).restrictScalars K.1) L.1 x)
  exact h.symm

end Square

end IdeleClassLimit

end

end GroundTheory.Global
end
