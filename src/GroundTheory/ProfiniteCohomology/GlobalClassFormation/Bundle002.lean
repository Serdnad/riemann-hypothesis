module

public import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality
public import GroundTheory.ProfiniteCohomology.Bundle009
public import GroundTheory.ProfiniteCohomology.InflationRestriction.Higher
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolNorm
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.Bundle001
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolReal
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolSep
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
import GroundTheory.GlobalFields.CyclotomicCharacters.Character
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.InfRange
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ClassLimitDefs
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.NormalFixingSubgroupGaloisClosure
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LevelDefs
public import GroundTheory.ProfiniteCohomology.Bundle004
import GroundTheory.ProfiniteCohomology.Bundle001
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.Bundle002
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.NatCardGroupCohomologyTwoIdeleClassRepDvd
public import GroundTheory.ProfiniteCohomology.InflationRestriction.DegreeOne
import GroundTheory.LocalFields.LocalArtinBaseChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

attribute [local instance 2000] Rep.hV2 Submodule.module Submodule.Quotient.module

section CyclicChar

variable (Q : Type) [Group Q] [Finite Q] [IsCyclic Q]

theorem exists_injective_addCircle_char : ∃ ψ : Additive Q →+ AddCircle (1 : ℚ), Function.Injective ψ := by
  have := Fintype.ofFinite Q
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Q)
  refine ⟨GroundTheory.GroupCoh.cyclicChar σ hσ, (injective_iff_map_eq_zero _).2 fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hσ (Additive.toMul x))
  have hxk : x = k • Additive.ofMul σ := by rw [← ofMul_zpow, hk, ofMul_toMul]
  rw [hxk, map_zsmul, GroundTheory.GroupCoh.cyclicChar_apply_gen] at hx
  have hn : (Nat.card Q : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h' : (((k : ℚ) * (1 / Nat.card Q) : ℚ) : AddCircle (1 : ℚ)) = 0 := by
    rw [← zsmul_eq_mul]
    exact hx
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff _).1 h'
  rw [zsmul_one] at hm
  have hkm : k = m * (Nat.card Q : ℤ) := by
    have : (k : ℚ) = m * Nat.card Q := by
      field_simp at hm
      linarith
    exact_mod_cast this
  rw [hxk, hkm, mul_comm, ← ofMul_zpow, zpow_mul, zpow_natCast, pow_card_eq_one', one_zpow, ofMul_one]

end CyclicChar

section Main

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

theorem exists_cupCharClassProf_eq_of_cohomologyRes_eq_zero (A : Rep ℤ G) [IsDiscreteRep A]
    (N : Subgroup G) [N.Normal] (hN : IsOpen (N : Set G)) [IsCyclic (G ⧸ N)]
    (h1 : IsZero (cohomology (Rep.res N.subtype A) 1)) (x : cohomology A 2)
    (hx : (cohomologyRes A N 2).hom x = 0) :
    ∃ (χ : Additive G →ₜ+ QZ) (a : A.ρ.invariants), (∀ n ∈ N, χ (Additive.ofMul n) = 0) ∧
      (cupCharClassProf A χ).hom a = x := by
  have hNc : IsClosed (N : Set G) := Subgroup.isClosed_of_isOpen N hN
  have hmem : x ∈ LinearMap.range (cohomologyInfl A N 2).hom := by
    rw [range_cohomologyInfl_eq_ker_cohomologyRes hNc two_ne_zero]
    · exact hx
    · intro i hi hi2
      obtain rfl : i = 1 := by omega
      exact h1
  obtain ⟨y, rfl⟩ := hmem
  have : DiscreteTopology (G ⧸ N) := QuotientGroup.discreteTopology hN
  have : Finite (G ⧸ N) := Subgroup.quotient_finite_of_isOpen N hN
  have := Fintype.ofFinite (G ⧸ N)
  obtain ⟨ψ, hψ⟩ := exists_injective_addCircle_char (G ⧸ N)
  let χ₀ : Additive (G ⧸ N) →ₜ+ QZ :=
    { toAddMonoidHom := QZ.toAddCircle.symm.toAddMonoidHom.comp ψ
      continuous_toFun := continuous_of_discreteTopology }
  have hχ₀ : Function.Injective χ₀ := QZ.toAddCircle.symm.injective.comp hψ
  obtain ⟨a, rfl⟩ := cupCharClassProf_surjective (A.quotientToInvariants N) χ₀ hχ₀ y
  let f : Rep.res (QuotientGroup.mk' N) (A.quotientToInvariants N) ⟶ A :=
    Rep.ofHom (A.ρ.quotientToInvariants_lift N)
  let b : A.ρ.invariants := ⟨f.hom (a : A.quotientToInvariants N), fun g => by
    have hc := Rep.hom_comm_apply f g (a : A.quotientToInvariants N)
    rw [← hc]
    congr 1
    exact a.2 (QuotientGroup.mk' N g)⟩
  refine ⟨contCharComp χ₀ (QuotientGroup.mk' N) (continuous_quotientGroup_mk' N), b, fun n hn => ?_, ?_⟩
  · rw [contCharComp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).2 hn, ofMul_one, map_zero]
  · rw [cohomologyInfl_eq]
    exact (cohomologyMapAlong_cupCharClassProf (QuotientGroup.mk' N) (continuous_quotientGroup_mk' N) f χ₀
      a b rfl).symm

end Main

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField GroundTheory.Global FiniteSubfield IsDedekindDomain

open scoped NumberField.LiesOver DirectSum

noncomputable section

variable {K : FiniteSubfield}

section Infinite

variable (v : InfinitePlace K.1)

theorem exists_infCompletion_algEquiv : ∃ (F : FiniteSubfield) (_ : Fact (K ≤ F)) (w : v.placesOver F.1),
    Nonempty ((w : InfinitePlace F.1).Completion ≃ₐ[v.Completion] AlgebraicClosure v.Completion) := by
  obtain ⟨ι⟩ : Nonempty (AlgebraicClosure ℚ →ₐ[K.1] AlgebraicClosure v.Completion) := nonempty_algHom_of_isSepClosed
  obtain ⟨p, hp⟩ := exists_level_infCompletionEmbedding_surjective ι
  exact ⟨p.1, inferInstance, infPlaceOfEmbedding ι p.1, ⟨AlgEquiv.ofBijective (infCompletionEmbedding ι p.1)
    ⟨(infCompletionEmbedding ι p.1).toRingHom.injective, hp p le_rfl⟩⟩⟩

instance finiteDimensional_infAlgClosure :
    FiniteDimensional v.Completion (AlgebraicClosure v.Completion) := by
  obtain ⟨F, _, w, ⟨e⟩⟩ := exists_infCompletion_algEquiv v
  have : (w : InfinitePlace F.1).LiesOver v := w.2
  exact LinearEquiv.finiteDimensional e.toLinearEquiv

instance charZero_infCompletion : CharZero v.Completion :=
  charZero_of_injective_algebraMap (algebraMap K.1 v.Completion).injective

instance isGalois_infAlgClosure : IsGalois v.Completion (AlgebraicClosure v.Completion) :=
  inferInstance

theorem infAlgClosure_finrank_le_two :
    Module.finrank v.Completion (AlgebraicClosure v.Completion) ≤ 2 := by
  obtain ⟨F, _, w, ⟨e⟩⟩ := exists_infCompletion_algEquiv v
  have : (w : InfinitePlace F.1).LiesOver v := w.2
  rw [← e.toLinearEquiv.finrank_eq]
  by_cases h : v.IsReal ∧ (w : InfinitePlace F.1).IsComplex
  · exact ((InfinitePlace.finrank_completion_eq_two_iff (w : InfinitePlace F.1)).2 h).le
  · rw [(InfinitePlace.finrank_completion_eq_one_iff (w : InfinitePlace F.1)).2 h]
    norm_num

theorem infAlgClosure_mul_mem_range_norm : ∀ a b : v.Completionˣ,
    (a : v.Completion) ∉ Set.range (Algebra.norm v.Completion : AlgebraicClosure v.Completion → v.Completion) →
    (b : v.Completion) ∉ Set.range (Algebra.norm v.Completion : AlgebraicClosure v.Completion → v.Completion) →
    ((a * b : v.Completionˣ) : v.Completion) ∈
      Set.range (Algebra.norm v.Completion : AlgebraicClosure v.Completion → v.Completion) := by
  obtain ⟨F, _, w, ⟨e⟩⟩ := exists_infCompletion_algEquiv v
  have : (w : InfinitePlace F.1).LiesOver v := w.2
  have hrange : Set.range (Algebra.norm v.Completion : AlgebraicClosure v.Completion → v.Completion) =
      Set.range (Algebra.norm v.Completion : (w : InfinitePlace F.1).Completion → v.Completion) := by
    ext c
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨e.symm y, Algebra.norm_eq_of_algEquiv e.symm y⟩
    · rintro ⟨y, rfl⟩
      exact ⟨e y, Algebra.norm_eq_of_algEquiv e y⟩
  have hmem : ∀ c : v.Completionˣ, (c : v.Completion) ∈
      Set.range (Algebra.norm v.Completion : (w : InfinitePlace F.1).Completion → v.Completion) ↔
      c ∈ InfinitePlace.normSubgroup v (w : InfinitePlace F.1) := by
    intro c
    constructor
    · rintro ⟨y, hy⟩
      have hy0 : y ≠ 0 := by
        rintro rfl
        rw [Algebra.norm_zero] at hy
        exact c.ne_zero hy.symm
      exact ⟨Units.mk0 y hy0, Units.ext hy⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, congrArg Units.val hy⟩
  intro a b ha hb
  rw [hrange, hmem] at ha hb ⊢
  by_cases h : v.IsReal ∧ (w : InfinitePlace F.1).IsComplex
  · rw [InfinitePlace.mem_normSubgroup_iff h.1 h.2] at ha hb ⊢
    have ha' : InfinitePlace.Completion.extensionEmbeddingOfIsReal h.1 (a : v.Completion) < 0 :=
      lt_of_le_of_ne (not_lt.1 ha) ((map_ne_zero _).2 a.ne_zero)
    have hb' : InfinitePlace.Completion.extensionEmbeddingOfIsReal h.1 (b : v.Completion) < 0 :=
      lt_of_le_of_ne (not_lt.1 hb) ((map_ne_zero _).2 b.ne_zero)
    rw [Units.val_mul, map_mul]
    exact mul_pos_of_neg_of_neg ha' hb'
  · exact absurd (InfinitePlace.normSubgroup_eq_top (w : InfinitePlace F.1) h ▸ Subgroup.mem_top a) ha

end Infinite

def placeInv : ∀ v : Place K.1, localGaloisCohomology K 2 v →+ QZ
  | .inl v => quadraticInv v.Completion (AlgebraicClosure v.Completion) (infAlgClosure_finrank_le_two v)
      (infAlgClosure_mul_mem_range_norm v)
  | .inr v => brauerInvZOfIsSepClosure (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))

theorem placeInv_injective : ∀ v : Place K.1, Function.Injective (placeInv v)
  | .inl v => quadraticInv_injective v.Completion (AlgebraicClosure v.Completion)
      (infAlgClosure_finrank_le_two v) (infAlgClosure_mul_mem_range_norm v)
  | .inr v => (brauerInvZOfIsSepClosure_bijective (v.adicCompletion K.1)
      (AlgebraicClosure (v.adicCompletion K.1))).1

theorem placeInv_bijective_inr (v : HeightOneSpectrum (𝓞 K.1)) :
    Function.Bijective (placeInv (K := K) (.inr v)) :=
  brauerInvZOfIsSepClosure_bijective (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))


variable (K) in
def sumPlaceInv : (⨁ v : Place K.1, localGaloisCohomology K 2 v) →+ QZ :=
  by classical exact DirectSum.toAddMonoid fun v => placeInv v


open Classical in
theorem sumPlaceInv_of (v : Place K.1) (t : localGaloisCohomology K 2 v) :
    sumPlaceInv K (DirectSum.of _ v t) = placeInv v t := by
  unfold sumPlaceInv
  convert DirectSum.toAddMonoid_of (fun v => placeInv (K := K) v) v t

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

section Level

variable {F : FiniteSubfield} [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]

set_option synthInstance.maxHeartbeats 400000 in
theorem classSmul_of_restrictHom (g : K.1.fixingSubgroup) (c : IdeleClassGroup F.1) :
    (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • IdeleClassLimit.of F c = IdeleClassLimit.of F (restrictHom (E := F) g • c) := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective F.1 c
  have hx := congrArg IdeleLimit.toClassLimit (smul_of_restrictHom g x)
  rw [IdeleLimit.toClassLimit_smul, IdeleLimit.toClassLimit_of, IdeleLimit.toClassLimit_of] at hx
  exact hx


variable (K F) in
def classLevelMor :
    Rep.res (restrictHom (F := K) (E := F)) (ideleClassRep K.1 F.1) ⟶ classLimitRep K :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (IdeleClassLimit.of F)).toIntLinearMap, fun g => LinearMap.ext fun x =>
    congrArg Additive.ofMul (classSmul_of_restrictHom g x.toMul).symm⟩


variable (K F) in
def classLevelInfl (n : ℕ) : cohomology (ideleClassRep K.1 F.1) n ⟶ cohomology (classLimitRep K) n :=
  cohomologyMapAlong restrictHom continuous_restrictHom (classLevelMor K F) n

end Level

section Transition

variable {F E : FiniteSubfield} [Fact (K ≤ F)] [Fact (K ≤ E)] [Fact (F ≤ E)]
  [F.1.fixingSubgroup.Normal] [E.1.fixingSubgroup.Normal]



end Transition

section Colimit

abbrev classLevelCochainsInfl (p : GLevel K) :
    cochainsComplex (ideleClassRep K.1 p.1.1) ⟶ cochainsComplex (classLimitRep K) :=
  cochainsMapAlong restrictHom continuous_restrictHom (classLevelMor K p.1)

theorem classLevelCochains_injective (p : GLevel K) (m : ℕ) :
    Function.Injective ((classLevelCochainsInfl p).f m).hom := by
  intro y y' h
  apply (ModuleCat.mono_iff_injective ((cochainsComplexι (ideleClassRep K.1 p.1.1)).f m)).1 inferInstance
  funext τ
  let σ : Fin m → K.1.fixingSubgroup := fun i =>
    Function.surjInv (restrictHom_surjective (F := K) (E := p.1)) (τ i)
  have hσ : (fun i => restrictHom (E := p.1) (σ i)) = τ :=
    funext fun i => Function.surjInv_eq (restrictHom_surjective (F := K) (E := p.1)) (τ i)
  have h1 := congrFun (congrArg (fun c => ((cochainsComplexι (classLimitRep K)).f m).hom c) h) σ
  simp only at h1
  change Additive.ofMul (IdeleClassLimit.of p.1 (((cochainsComplexι _).f m).hom y
      (fun i => restrictHom (E := p.1) (σ i))).toMul) =
    Additive.ofMul (IdeleClassLimit.of p.1 (((cochainsComplexι _).f m).hom y'
      (fun i => restrictHom (E := p.1) (σ i))).toMul) at h1
  rw [hσ] at h1
  exact congrArg Additive.ofMul (IdeleClassLimit.of_injective p.1 (congrArg Additive.toMul h1))

theorem exists_classLevelCochains_eq (m : ℕ) (x : (cochainsComplex (classLimitRep K)).X m) :
    ∃ (p : GLevel K) (y : (cochainsComplex (ideleClassRep K.1 p.1.1)).X m),
      ((classLevelCochainsInfl p).f m).hom y = x := by
  classical
  have hx : IsLocallyConstant (((cochainsComplexι (classLimitRep K)).f m).hom x :
      (Fin m → K.1.fixingSubgroup) → classLimitRep K) :=
    (show locallyConstantCochains (classLimitRep K) m from x).2
  set f := ((cochainsComplexι (classLimitRep K)).f m).hom x with hf
  obtain ⟨U, hU⟩ := exists_openNormalSubgroup_fin_of_isLocallyConstant hx
  obtain ⟨t, ht, htU⟩ := isOpen_induced_iff.1 U.isOpen
  have h1t : (1 : ℚ̄ ≃ₐ[ℚ] ℚ̄) ∈ t := by
    have : (1 : K.1.fixingSubgroup) ∈ Subtype.val ⁻¹' t := by
      rw [htU]
      exact U.one_mem
    exact this
  obtain ⟨E₀, hE₀fin, hE₀⟩ := (krullTopology_mem_nhds_one_iff ℚ ℚ̄ t).1 (ht.mem_nhds h1t)
  have hfin : (Set.range f).Finite := hx.range_finite
  choose idx x' hx' using fun a : classLimitRep K => IdeleClassLimit.exists_of (Additive.toMul a)
  choose lev hlev using fun E : FiniteSubfield => GLevel.exists_le (K := K) E
  have : Nonempty (GLevel K) := ⟨lev K⟩
  have : IsDirectedOrder (GLevel K) := ⟨fun p q => by
    let E : FiniteSubfield := ⟨p.1.1 ⊔ q.1.1, inferInstance⟩
    exact ⟨lev E, (show p.1.1 ≤ p.1.1 ⊔ q.1.1 from le_sup_left).trans (hlev E),
      (show q.1.1 ≤ p.1.1 ⊔ q.1.1 from le_sup_right).trans (hlev E)⟩⟩
  obtain ⟨p, hp⟩ := Finset.exists_le ((hfin.toFinset.image fun a => lev (idx a)) ∪
    {lev ⟨E₀, hE₀fin⟩})
  have hpE₀ : E₀ ≤ p.1.1 := (hlev ⟨E₀, hE₀fin⟩).trans
    (hp _ (Finset.mem_union_right _ (Finset.mem_singleton_self _)))
  have hker : ∀ g : K.1.fixingSubgroup, restrictHom (E := p.1) g = 1 → g ∈ U := by
    intro g hg
    have hg' : g ∈ p.1.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup := by
      rw [← ker_restrictHom, MonoidHom.mem_ker]
      exact hg
    rw [Subgroup.mem_subgroupOf] at hg'
    have : g ∈ Subtype.val ⁻¹' t := hE₀ (IntermediateField.fixingSubgroup_le hpE₀ hg')
    rw [htU] at this
    exact this
  have hval : ∀ g, ∃ z : IdeleClassGroup p.1.1, IdeleClassLimit.of p.1 z = Additive.toMul (f g) := by
    intro g
    have hmem : f g ∈ hfin.toFinset := by simp
    have hle : idx (f g) ≤ p.1 := (hlev (idx (f g))).trans
      (hp _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hmem)))
    exact ⟨ideleClassMap hle (x' (f g)), by rw [IdeleClassLimit.of_ideleClassMap]; exact hx' _⟩
  choose z hz using hval
  let lift : (Fin m → (p.1.1 ≃ₐ[K.1] p.1.1)) → Fin m → K.1.fixingSubgroup := fun τ i =>
    Function.surjInv (restrictHom_surjective (F := K) (E := p.1)) (τ i)
  refine ⟨p, ⟨fun τ => Additive.ofMul (z (lift τ)), IsLocallyConstant.of_discrete _⟩, ?_⟩
  apply (ModuleCat.mono_iff_injective ((cochainsComplexι (classLimitRep K)).f m)).1 inferInstance
  funext g
  change Additive.ofMul (IdeleClassLimit.of p.1 (z (lift fun i => restrictHom (E := p.1) (g i)))) = f g
  rw [hz]
  refine hU _ _ fun i => hker _ ?_
  rw [map_mul, map_inv, Function.surjInv_eq (restrictHom_surjective (F := K) (E := p.1)),
    inv_mul_cancel]

theorem exists_classLevelInfl_eq (n : ℕ) (x : cohomology (classLimitRep K) n) :
    ∃ (p : GLevel K) (y : cohomology (ideleClassRep K.1 p.1.1) n), (classLevelInfl K p.1 n).hom y = x := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((cochainsComplex (classLimitRep K)).homologyπ n)).1 inferInstance x
  obtain ⟨p, y₀, hy₀⟩ := exists_classLevelCochains_eq n
    (((cochainsComplex (classLimitRep K)).iCycles n).hom z)
  have hd : ((cochainsComplex (ideleClassRep K.1 p.1.1)).d n (n + 1)).hom y₀ = 0 := by
    apply classLevelCochains_injective p (n + 1)
    rw [map_zero, hom_f_d_apply, hy₀]
    exact iCycles_d_apply _ n (n + 1) z
  obtain ⟨w, hw⟩ := exists_iCycles_eq_of_d_eq_zero _ n y₀ hd
  refine ⟨p, ((cochainsComplex (ideleClassRep K.1 p.1.1)).homologyπ n).hom w, ?_⟩
  refine (homologyMap_homologyπ_apply (classLevelCochainsInfl p) n w).trans (congrArg _ ?_)
  apply (ModuleCat.mono_iff_injective ((cochainsComplex (classLimitRep K)).iCycles n)).1 inferInstance
  rw [iCycles_cyclesMap_apply, hw, hy₀]


end Colimit


variable (K) in
theorem isZero_cohomology_one_classLimitRep : Limits.IsZero (cohomology (classLimitRep K) 1) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  have hz : ∀ x : cohomology (classLimitRep K) 1, x = 0 := by
    intro x
    obtain ⟨p, y, rfl⟩ := exists_classLevelInfl_eq 1 x
    have h0 : Limits.IsZero (cohomology (ideleClassRep K.1 p.1.1) 1) :=
      isZero_groupCohomology_one_ideleClassRep.of_iso (cohomologyIsoGroupCohomology _ 1)
    rw [ModuleCat.isZero_iff_subsingleton] at h0
    rw [Subsingleton.elim y 0, map_zero]
  exact ⟨fun x y => by rw [hz x, hz y]⟩

end

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IntermediateField GroundTheory.LocalField

noncomputable section

variable (Kv Ω : Type) [Field Kv] [ValuativeRel Kv] [TopologicalSpace Kv] [IsNonarchimedeanLocalField Kv]
  [Field Ω] [Algebra Kv Ω] [IsSepClosure Kv Ω] (L : IntermediateField Kv Ω)

def galUnitsZResScalars :
    Rep.res (AlgEquiv.restrictScalarsHom Kv : Gal(Ω/L) →* Gal(Ω/Kv)) (galUnitsZ Kv Ω) ⟶ galUnitsZ L Ω :=
  Rep.ofHom ⟨LinearMap.id, fun _ => LinearMap.ext fun _ => rfl⟩

def brauerResZ : cohomology (galUnitsZ Kv Ω) 2 ⟶ cohomology (galUnitsZ L Ω) 2 :=
  cohomologyMapAlong (AlgEquiv.restrictScalarsHom Kv) (continuous_restrictScalarsHom_of_tower Kv L Ω)
    (galUnitsZResScalars Kv Ω L) 2

theorem brauerResZ_eq_zero_of_finrank_smul [FiniteDimensional Kv L] (y : cohomology (galUnitsZ Kv Ω) 2)
    (hy : Module.finrank Kv L • brauerInvZOfIsSepClosure Kv Ω y = 0) : (brauerResZ Kv Ω L).hom y = 0 := by
  let := algebraicValuativeRel Kv Ω
  let := algebraicTopology Kv Ω
  have := algebraicTopology_isValuativeTopology Kv Ω
  have := algebraicValuativeRel_valuativeExtension Kv Ω
  obtain ⟨x, rfl⟩ := (cohomologyULiftIntAddEquiv (galUnits.{0} Kv Ω) 2).surjective y
  have e := cohomologyULiftIntAddEquiv_cohomologyMapAlong (galUnits.{0} Kv Ω)
    (AlgEquiv.restrictScalarsHom Kv) (continuous_restrictScalarsHom_of_tower Kv L Ω)
    (galUnitsResScalars Kv L Ω) (galUnitsZResScalars Kv Ω L) (fun _ => rfl) 2 x
  have h0 : brauerInvZOfIsSepClosure Kv Ω (cohomologyULiftIntAddEquiv (galUnits.{0} Kv Ω) 2 x) =
      brauerInv Kv Ω x :=
    brauerInvZ_cohomologyULiftIntAddEquiv Kv Ω x
  have h1 : brauerInv L Ω ((brauerRes Kv L Ω).hom x) = 0 := by
    rw [brauerInv_brauerRes, ← h0]
    exact hy
  have h2 : (brauerRes Kv L Ω).hom x = 0 :=
    (brauerInv_bijective L Ω).1 (h1.trans (map_zero _).symm)
  have h3 : cohomologyULiftIntAddEquiv (galUnits.{0} L Ω) 2 ((brauerRes Kv L Ω).hom x) = 0 := by
    rw [h2, map_zero]
  rw [brauerRes_eq] at h3
  exact e.symm.trans h3

end

end GroundTheory.ProfCoh
end
