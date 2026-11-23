module

public import GroundTheory.LocalFields.SeparableClosure
public import GroundTheory.LocalFields.UnramifiedExistence
public import GroundTheory.ProfiniteCohomology.GaloisCohomology.Brauer
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.OrderScalars
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.Unramified
public import GroundTheory.LocalFields.MaximalUnramified
public import GroundTheory.ProfiniteCohomology.GaloisModules.CoeGalRootsOfUnityHomApply
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import GroundTheory.LocalFields.IntermediateField
public import GroundTheory.LocalFields.Bundle006
public import GroundTheory.ProfiniteCohomology.GaloisCohomology.IsZeroGroupCohomologyQuotientToInvariantsGalAdd
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.OrderCyclic
public import GroundTheory.TateCohomology.Bundle003
import Mathlib.Algebra.Lie.OfAssociative
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IntermediateField GroundTheory.LocalField ValuativeRel

variable (F Ω : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field Ω] [Algebra F Ω] [IsSepClosure F Ω]

section Root

noncomputable def unramifiedRoot (n : ℕ+) : Ω :=
  haveI := IsSepClosure.sep_closed F (K := Ω)
  (exists_isPrimitiveRoot_card_pow_sub_one (K := F) (Ksep := Ω) n.ne_zero).choose

theorem isPrimitiveRoot_unramifiedRoot (n : ℕ+) :
    IsPrimitiveRoot (unramifiedRoot F Ω n) (Nat.card 𝓀[F] ^ (n : ℕ) - 1) :=
  haveI := IsSepClosure.sep_closed F (K := Ω)
  (exists_isPrimitiveRoot_card_pow_sub_one (K := F) (Ksep := Ω) n.ne_zero).choose_spec

noncomputable def unramifiedLevel (n : ℕ+) : IntermediateField F Ω :=
  F⟮unramifiedRoot F Ω n⟯

theorem unramifiedLevel_eq (n : ℕ+) : unramifiedLevel F Ω n = F⟮unramifiedRoot F Ω n⟯ :=
  rfl

theorem isUnramifiedSubextension_unramifiedLevel (n : ℕ+) :
    IsUnramifiedSubextension (unramifiedLevel F Ω n) :=
  (isUnramifiedSubextension_adjoin n.ne_zero (isPrimitiveRoot_unramifiedRoot F Ω n)).1

theorem finrank_unramifiedLevel (n : ℕ+) : Module.finrank F (unramifiedLevel F Ω n) = n :=
  (isUnramifiedSubextension_adjoin n.ne_zero (isPrimitiveRoot_unramifiedRoot F Ω n)).2

instance finiteDimensional_unramifiedLevel (n : ℕ+) :
    FiniteDimensional F (unramifiedLevel F Ω n) :=
  (isUnramifiedSubextension_unramifiedLevel F Ω n).1

instance isGalois_unramifiedLevel (n : ℕ+) : IsGalois F (unramifiedLevel F Ω n) :=
  IsUnramifiedSubextension.isGalois (isUnramifiedSubextension_unramifiedLevel F Ω n)

theorem unramifiedLevel_le {m n : ℕ+} (h : (m : ℕ) ∣ n) :
    unramifiedLevel F Ω m ≤ unramifiedLevel F Ω n :=
  haveI := IsSepClosure.sep_closed F (K := Ω)
  IsUnramifiedSubextension.le_adjoin (isUnramifiedSubextension_unramifiedLevel F Ω m) n.ne_zero
    ((finrank_unramifiedLevel F Ω m).symm ▸ h) (isPrimitiveRoot_unramifiedRoot F Ω n)

end Root

section Structure

variable [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension F Ω]

instance isUnramified_unramifiedLevel (n : ℕ+) : IsUnramified F (unramifiedLevel F Ω n) :=
  ⟨IsUnramifiedSubextension.ramificationIndex_eq_one (isUnramifiedSubextension_unramifiedLevel F Ω n)⟩

noncomputable def unramifiedLevelInv (n : ℕ+) :
    groupCohomology (galUnits F (unramifiedLevel F Ω n)) 2 →+ QZ :=
  (unramifiedInv F (unramifiedLevel F Ω n)).comp
    (h2GalUnitsAddEquiv F (unramifiedLevel F Ω n)).toAddMonoidHom

theorem unramifiedLevelInv_apply (n : ℕ+) (y : groupCohomology (galUnits F (unramifiedLevel F Ω n)) 2) :
    unramifiedLevelInv F Ω n y =
      unramifiedInv F (unramifiedLevel F Ω n) (h2GalUnitsAddEquiv F (unramifiedLevel F Ω n) y) :=
  rfl

noncomputable def brauerInvFun (x : galoisBrauerGroup F Ω) : QZ :=
  open Classical in
  if h : ∃ (n : ℕ+) (y : groupCohomology (galUnits F (unramifiedLevel F Ω n)) 2),
      (brauerInflation (unramifiedLevel F Ω n)).hom y = x then
    unramifiedLevelInv F Ω h.choose h.choose_spec.choose
  else 0

end Structure

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory CategoryTheory.Limits IntermediateField

universe u

section Transport

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

noncomputable def subgroupEquivGalFixedField (H : Subgroup Gal(L/K)) :
    H ≃* Gal(L/fixedField H) :=
  (MulEquiv.subgroupCongr (fixingSubgroup_fixedField H).symm).trans
    (fixingSubgroupEquiv (fixedField H))

noncomputable def groupCohomologyResGalUnitsIso (H : Subgroup Gal(L/K)) (n : ℕ) :
    groupCohomology (Rep.res H.subtype (galUnits.{u} K L)) n ≅
      groupCohomology (galUnits.{u} (fixedField H) L) n :=
  groupCohomology.mapIso (subgroupEquivGalFixedField H) (LinearEquiv.refl _ _)
    (fun _ => LinearMap.ext fun _ => rfl) n

theorem isZero_groupCohomology_one_res_galUnits (H : Subgroup Gal(L/K)) :
    IsZero (groupCohomology (Rep.res H.subtype (galUnits.{u} K L)) 1) :=
  (isZero_groupCohomology_one_galUnits (fixedField H) L).of_iso
    (groupCohomologyResGalUnitsIso H 1)

end Transport

section Step

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

def openNormalOfNormal (N : Subgroup Gal(L/K)) [N.Normal] : OpenNormalSubgroup Gal(L/K) where
  toSubgroup := N
  isOpen' := isOpen_discrete _
  isNormal' := inferInstance

theorem natCard_groupCohomology_two_galUnits_dvd_of_normal (N : Subgroup Gal(L/K)) [N.Normal]
    (hLE : Nat.card (groupCohomology (galUnits.{u} (fixedField N) L) 2) ∣
      Module.finrank (fixedField N) L)
    (hEK : Nat.card (groupCohomology (galUnits.{u} K (fixedField N)) 2) ∣
      Module.finrank K (fixedField N)) :
    Nat.card (groupCohomology (galUnits.{u} K L) 2) ∣ Module.finrank K L := by
  have h1 := isZero_groupCohomology_one_res_galUnits (K := K) (L := L) N
  have hinj := GroundTheory.GroupCoh.inflation_two_injective (A := galUnits.{u} K L) (S := N) h1
  have hex := GroundTheory.GroupCoh.range_inflation_two_eq_ker_restriction (A := galUnits.{u} K L) (S := N) h1
  set res := (GroundTheory.GroupCoh.restriction (galUnits.{u} K L) N 2).hom
  set infl := (GroundTheory.GroupCoh.inflation (galUnits.{u} K L) N 2).hom

  have hcard : Nat.card (groupCohomology (galUnits.{u} K L) 2) =
      Nat.card (LinearMap.range res) * Nat.card (LinearMap.ker res) := by
    rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker res),
      Nat.card_congr (LinearMap.quotKerEquivRange res).toEquiv, mul_comm]

  have hker : Nat.card (LinearMap.ker res) =
      Nat.card (groupCohomology (galUnits.{u} K (fixedField N)) 2) := by
    rw [← hex, ← Nat.card_congr (LinearEquiv.ofInjective infl hinj).toEquiv]
    exact Nat.card_congr (groupCohomologyQuotientGalUnitsIso (openNormalOfNormal N) 2).toLinearEquiv.toEquiv

  have hrange : Nat.card (LinearMap.range res) ∣
      Nat.card (groupCohomology (galUnits.{u} (fixedField N) L) 2) := by
    rw [← Nat.card_congr (groupCohomologyResGalUnitsIso N 2).toLinearEquiv.toEquiv]
    exact AddSubgroup.card_addSubgroup_dvd_card (LinearMap.range res).toAddSubgroup
  rw [hcard, hker, ← (letI : Module.Free (fixedField N) L := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank K (fixedField N) L), mul_comm (Module.finrank K _)]
  exact Nat.mul_dvd_mul (hrange.trans hLE) hEK

end Step

section Solvable

theorem exists_normal_ne_bot_ne_top_of_not_isCyclic {G : Type*} [Group G] [Group.IsSolvable G]
    (h : ¬IsCyclic G) : ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  by_contra hN
  push Not at hN
  have : Nontrivial G := by
    by_contra ht
    rw [not_nontrivial_iff_subsingleton] at ht
    exact h inferInstance
  have : IsSimpleGroup G :=
    { eq_bot_or_eq_top_of_normal := fun N hN' => by
        by_cases hb : N = ⊥
        · exact Or.inl hb
        · exact Or.inr (hN N hN' hb) }
  have hcomm := (IsSimpleGroup.comm_iff_isSolvable (G := G)).2 inferInstance
  let _ : CommGroup G := { (inferInstance : Group G) with mul_comm := hcomm }
  exact h IsSimpleGroup.isCyclic

end Solvable

section Bound

theorem natCard_groupCohomology_two_galUnits_dvd_of_finrank (n : ℕ) :
    ∀ (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
      [IsNonarchimedeanLocalField K]
      [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
      [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L],
      Module.finrank K L = n → Nat.card (groupCohomology (galUnits.{u} K L) 2) ∣ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ hn
  subst hn
  by_cases hcyc : IsCyclic Gal(L/K)
  · exact (natCard_groupCohomology_two_galUnits_of_isCyclic (K := K) (L := L)).dvd
  have := GroundTheory.LocalField.isSolvable_algEquiv (K := K) (L := L)
  obtain ⟨N, hN, hbot, htop⟩ := exists_normal_ne_bot_ne_top_of_not_isCyclic hcyc
  have hpos : 0 < Module.finrank K (fixedField N) := Module.finrank_pos
  have hLE : Module.finrank (fixedField N) L = Nat.card N := finrank_fixedField_eq_card N
  have hmul := (letI : Module.Free (fixedField N) L := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank K (fixedField N) L)
  have hcardG : Nat.card Gal(L/K) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  have hNlt : Nat.card N < Module.finrank K L := by
    rw [← hcardG]
    exact lt_of_le_of_ne (Subgroup.card_le_card_group N)
      fun h => htop ((Subgroup.card_eq_iff_eq_top N).1 h)
  have hN1 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).2 hbot
  apply natCard_groupCohomology_two_galUnits_dvd_of_normal N
  · exact ih _ (by rw [hLE]; exact hNlt) (fixedField N) L rfl
  · refine ih _ ?_ K (fixedField N) rfl
    rw [← hmul, hLE]
    exact lt_mul_right hpos hN1

end Bound

section Main

variable {K L : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]

theorem natCard_groupCohomology_two_galUnits_dvd :
    Nat.card (groupCohomology (galUnits.{u} K L) 2) ∣ Module.finrank K L :=
  natCard_groupCohomology_two_galUnits_dvd_of_finrank _ K L rfl

theorem finite_groupCohomology_two_galUnits :
    Finite (groupCohomology (galUnits.{u} K L) 2) :=
  Nat.finite_of_card_ne_zero fun h =>
    Module.finrank_pos.ne' (Nat.eq_zero_of_zero_dvd (h ▸ natCard_groupCohomology_two_galUnits_dvd))

end Main

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory GroundTheory.LocalField ValuativeRel

instance valuativeExtension_self (F : Type*) [Field F] [ValuativeRel F] : ValuativeExtension F F :=
  ⟨fun {_ _} => Iff.rfl⟩

section Tower

variable (K K' L L' : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  [IsUnramified K L] [Field K'] [Field L'] [Algebra K K'] [Algebra K L'] [Algebra K' L']
  [Algebra L L'] [IsScalarTower K K' L'] [IsScalarTower K L L']

noncomputable def galRestrict : Gal(L'/K') →* Gal(L/K) :=
  haveI : IsGalois K L := isGalois_of_unramified K L IsUnramified.ramificationIndex_eq_one
  (AlgEquiv.restrictNormalHom L).comp
    { toFun := fun σ : Gal(L'/K') => AlgEquiv.restrictScalars K σ
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem algebraMap_galRestrict_apply (σ : Gal(L'/K')) (x : L) :
    algebraMap L L' (galRestrict K K' L L' σ x) = σ (algebraMap L L' x) := by
  have : IsGalois K L := isGalois_of_unramified K L IsUnramified.ramificationIndex_eq_one
  exact AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars K σ) L x

noncomputable def unitsResHom :
    Rep.res (galRestrict K K' L L') (galUnitsZ K L) ⟶ galUnitsZ K' L' :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (Units.map (algebraMap L L' : L →* L'))).toIntLinearMap,
    fun σ => by
      ext x
      exact algebraMap_galRestrict_apply K K' L L' σ _⟩

noncomputable abbrev unitsResH2 :
    groupCohomology (galUnitsZ K L) 2 ⟶ groupCohomology (galUnitsZ K' L') 2 :=
  groupCohomology.map (galRestrict K K' L L') (unitsResHom K K' L L') 2

variable [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K'] [ValuativeRel L']
  [TopologicalSpace L'] [IsNonarchimedeanLocalField L'] [ValuativeExtension K K']
  [ValuativeExtension K' L'] [ValuativeExtension L L'] [FiniteDimensional K K']
  [FiniteDimensional K' L'] [IsUnramified K' L']


omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [FiniteDimensional K L] in
theorem ramificationIndex_right_eq :
    (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L'))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) = (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation K'))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) := by
  have : ValuativeExtension K L' := valuativeExtension_trans K K' L'
  have : FiniteDimensional K L' := FiniteDimensional.trans K K' L'
  have : FiniteDimensional L L' := FiniteDimensional.right K L L'
  have h1 := ramificationIndex_tower K L L'
  have h2 := ramificationIndex_tower K K' L'
  have hKL : ramificationIndex K L = 1 := IsUnramified.ramificationIndex_eq_one
  have hK'L' : ramificationIndex K' L' = 1 := IsUnramified.ramificationIndex_eq_one
  rw [hKL, one_mul] at h1
  rw [hK'L', mul_one] at h2
  exact h1.symm.trans h2

theorem card_residueField_eq_pow : Nat.card 𝓀[K'] = Nat.card 𝓀[K] ^ ((IsLocalRing.maximalIdeal 𝒪[K']).inertiaDeg (𝒪[K])) := by
  let := Fintype.ofFinite 𝓀[K]
  let := Fintype.ofFinite 𝓀[K']
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := 𝓀[K]) (V := 𝓀[K']), residueDegree_eq_finrank]

theorem galRestrict_frob : galRestrict K K' L L' (frob K' L') = frob K L ^ ((IsLocalRing.maximalIdeal 𝒪[K']).inertiaDeg (𝒪[K])) := by
  have he := IsUnramified.ramificationIndex_eq_one (K := K) (L := L)
  apply residueAlgEquiv_injective_of_unramified K L he
  ext y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  have hpow : ∀ n : ℕ, residueAlgEquiv K L (frob K L ^ n) (IsLocalRing.residue 𝒪[L] x) =
      IsLocalRing.residue 𝒪[L] x ^ (Nat.card 𝓀[K] ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', map_mul, AlgEquiv.mul_apply, ih, map_pow, residueAlgEquiv_frobenius_apply,
        ← pow_mul, pow_succ, mul_comm]
  rw [hpow, ← card_residueField_eq_pow K K', residueAlgEquiv_residue]
  apply (algebraMap 𝓀[L] 𝓀[L']).injective
  rw [map_pow, IsLocalRing.ResidueField.algebraMap_residue,
    IsLocalRing.ResidueField.algebraMap_residue]
  have hx : algebraMap 𝒪[L] 𝒪[L'] (integerAlgEquiv K L (galRestrict K K' L L' (frob K' L')) x) =
      integerAlgEquiv K' L' (frob K' L') (algebraMap 𝒪[L] 𝒪[L'] x) :=
    Subtype.ext (algebraMap_galRestrict_apply K K' L L' _ _)
  rw [hx, residue_frobenius_apply]

theorem unitsResH2_comp_h2Valuation :
    unitsResH2 K K' L L' ≫ h2Valuation K' L' =
      h2Valuation K L ≫ groupCohomology.map (galRestrict K K' L L')
        (intMulRes (galRestrict K K' L L') ((_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation K'))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))))) 2 := by
  have : FiniteDimensional K L' := FiniteDimensional.trans K K' L'
  have : FiniteDimensional L L' := FiniteDimensional.right K L L'
  simp only [h2Valuation, groupCohomology.functor_map]
  rw [← groupCohomology.map_comp, ← groupCohomology.map_comp]
  refine groupCohomology.map_congr (by ext; rfl) (LinearMap.ext fun x => ?_) 2
  change ord (algebraMap L L' ((Additive.toMul x : Lˣ) : L)) =
    ((_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation K'))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) : ℤ) * ord ((Additive.toMul x : Lˣ) : L)
  rw [ord_algebraMap, ramificationIndex_right_eq K K' L L']

theorem unramifiedInv_unitsResH2 (x : groupCohomology (galUnitsZ K L) 2) :
    unramifiedInv K' L' ((unitsResH2 K K' L L').hom x) =
      Module.finrank K K' • unramifiedInv K L x := by
  have hsq := congrArg (fun h => h.hom x) (unitsResH2_comp_h2Valuation K K' L L')
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hsq
  rw [unramifiedInv_apply, hsq, h2IntAddEquiv_map_intMulRes, unramifiedInv_apply,
    AddMonoidHom.smul_apply, AddMonoidHom.comp_apply, MonoidHom.toAdditive_apply_apply,
    toMul_ofMul, galRestrict_frob, ofMul_pow, map_nsmul, map_zsmul, map_nsmul,
    ← ramificationIndex_mul_residueDegree K K', mul_nsmul', natCast_zsmul]

end Tower

section Inflation

variable (K L L' : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Field L'] [ValuativeRel L'] [TopologicalSpace L']
  [IsNonarchimedeanLocalField L'] [Algebra K L] [Algebra K L'] [Algebra L L']
  [IsScalarTower K L L'] [ValuativeExtension K L] [ValuativeExtension K L']
  [ValuativeExtension L L'] [FiniteDimensional K L] [FiniteDimensional K L'] [IsUnramified K L]
  [IsUnramified K L']

theorem unramifiedInv_inflation (x : groupCohomology (galUnitsZ K L) 2) :
    unramifiedInv K L' ((unitsResH2 K K L L').hom x) = unramifiedInv K L x := by
  rw [unramifiedInv_unitsResH2, Module.finrank_self, one_smul]

end Inflation

end GroundTheory.ProfCoh
end
