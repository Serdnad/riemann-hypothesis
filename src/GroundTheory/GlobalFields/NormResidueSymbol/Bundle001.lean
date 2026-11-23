module

public import GroundTheory.GlobalFields.IdeleGroups.Rational
public import GroundTheory.GlobalFields.CyclotomicCharacters.ProfinitePadic
public import GroundTheory.GlobalFields.NormResidueSymbol.Abstract
public import Mathlib.Order.CompletePartialOrder
import GroundTheory.GlobalFields.Adele.Bundle002
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup IntermediateField
open scoped GroundTheory.LocalField.Abstract

noncomputable section

namespace RationalSymbol

open _root_.GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract

instance isGalois_maxCyclotomic : IsGalois ℚ maxCyclotomic := by
  have : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)
  have h : @IsGalois ℚ _ maxCyclotomic _ (IntermediateField.algebra' maxCyclotomic) := by
    rw [← InfiniteGalois.normal_iff_isGalois, ← ker_character]
    infer_instance
  convert h

abbrev cycRestrict : Gal(AlgebraicClosure ℚ/ℚ) →* Gal(maxCyclotomic/ℚ) :=
  AlgEquiv.restrictNormalHom maxCyclotomic

theorem cycRestrict_surjective : Function.Surjective cycRestrict := by
  have : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)
  exact AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := maxCyclotomic)
    (E := AlgebraicClosure ℚ)

theorem coe_cycRestrict_apply (σ : Gal(AlgebraicClosure ℚ/ℚ)) (x : maxCyclotomic) :
    ((cycRestrict σ x : maxCyclotomic) : AlgebraicClosure ℚ) = σ x :=
  AlgEquiv.restrictNormal_commutes σ maxCyclotomic x

theorem ker_cycRestrict : cycRestrict.ker = character.ker := by
  rw [ker_character]
  ext σ
  rw [MonoidHom.mem_ker, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have := coe_cycRestrict_apply σ ⟨x, hx⟩
    rw [h, AlgEquiv.one_apply] at this
    exact this.symm
  · intro h
    ext x
    rw [coe_cycRestrict_apply, AlgEquiv.one_apply]
    exact h x x.2

def cycCharacter : Gal(maxCyclotomic/ℚ) ≃* ℤ̂ˣ :=
  (QuotientGroup.quotientKerEquivOfSurjective cycRestrict cycRestrict_surjective).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq ker_cycRestrict).trans
      (QuotientGroup.quotientKerEquivOfSurjective character character_surjective))

theorem cycCharacter_cycRestrict (σ : Gal(AlgebraicClosure ℚ/ℚ)) : cycCharacter (cycRestrict σ) = character σ := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective cycRestrict cycRestrict_surjective).symm
      (cycRestrict σ) = (σ : Gal(AlgebraicClosure ℚ/ℚ) ⧸ cycRestrict.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [cycCharacter, MulEquiv.trans_apply, MulEquiv.trans_apply, h]
  rfl

theorem cycCharacter_spec (τ : Gal(maxCyclotomic/ℚ)) (n : ℕ+) {ζ : maxCyclotomic}
    (hζ : ζ ^ (n : ℕ) = 1) :
    τ ζ = ζ ^ (ProfiniteInteger.proj n (cycCharacter τ : ℤ̂)).val := by
  obtain ⟨σ, rfl⟩ := cycRestrict_surjective τ
  apply Subtype.ext
  rw [cycCharacter_cycRestrict, SubmonoidClass.coe_pow]
  rw [coe_cycRestrict_apply]
  exact character_spec σ n (by rw [← SubmonoidClass.coe_pow, hζ, OneMemClass.coe_one])

def unitPart : IdeleClassGroup ℚ →* ℤ̂ˣ :=
  (Units.map padicEquiv.symm.toRingHom.toMonoidHom).comp
    ((MonoidHom.snd _ _).comp _root_.GroundTheory.Global.RationalIdeles.ideleClassGroupEquiv.toMulEquiv.toMonoidHom)

theorem toPadicInt_unitPart (x : IdeleClassGroup ℚ) (q : Nat.Primes) :
    toPadicInt q (unitPart x : ℤ̂) =
      ((_root_.GroundTheory.Global.RationalIdeles.ideleClassGroupEquiv x).2 : Π p : Nat.Primes, ℤ_[p]) q := by
  change toPadics (padicEquiv.symm _) q = _
  rw [← padicEquiv_apply, RingEquiv.apply_symm_apply]
  rfl

def reciprocityMap : IdeleClassGroup ℚ →* Gal(maxCyclotomic/ℚ) :=
  cycCharacter.symm.toMonoidHom.comp unitPart⁻¹

theorem cycCharacter_reciprocityMap (x : IdeleClassGroup ℚ) :
    cycCharacter (reciprocityMap x) = (unitPart x)⁻¹ := by
  simp [reciprocityMap]

end RationalSymbol

end

end GroundTheory.Global
end

section

namespace GroundTheory.Global

open Filter Topology NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

noncomputable section

namespace IdeleGroup

variable (K : Type*) [Field K] [NumberField K]

def localEmbeddingSubgroup : Subgroup (IdeleGroup K) :=
  (⨆ v : HeightOneSpectrum (𝓞 K), (finiteEmbedding v).range) ⊔
    ⨆ w : InfinitePlace K, (infiniteEmbedding w).range

variable {K}

theorem finiteEmbedding_mem_localEmbeddingSubgroup (v : HeightOneSpectrum (𝓞 K))
    (a : (v.adicCompletion K)ˣ) : finiteEmbedding v a ∈ localEmbeddingSubgroup K :=
  Subgroup.mem_sup_left (Subgroup.mem_iSup_of_mem v ⟨a, rfl⟩)

theorem infiniteEmbedding_mem_localEmbeddingSubgroup (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    infiniteEmbedding w a ∈ localEmbeddingSubgroup K :=
  Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem w ⟨a, rfl⟩)

theorem exists_mem_localEmbeddingSubgroup_inv_mul_mem {N : Set (IdeleGroup K)} (hN : N ∈ 𝓝 1)
    (x : IdeleGroup K) : ∃ h ∈ localEmbeddingSubgroup K, h⁻¹ * x ∈ N := by
  classical
  obtain ⟨_, ⟨U, V, -, -, hVO, rfl⟩, h1, htN⟩ := (isTopologicalBasis K).mem_nhds_iff.1 hN
  have hU1 : ∀ w, (1 : (w.Completion)ˣ) ∈ U w := fun w ↦ by simpa using h1.1 w
  have hV1 : ∀ v, (1 : (v.adicCompletion K)ˣ) ∈ V v := fun v ↦ by simpa using h1.2 v
  have hS : {v : HeightOneSpectrum (𝓞 K) | ¬ (V v =
      ((Submonoid.ofClass (v.adicCompletionIntegers K)).units : Set (v.adicCompletion K)ˣ) ∧
        finiteProj v x ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units)}.Finite :=
    eventually_cofinite.1 (hVO.and (eventually_finiteProj_mem_units x))
  set S := hS.toFinset with hSdef
  set h : IdeleGroup K := (∏ w, infiniteEmbedding w (infiniteProj w x)) *
    ∏ v ∈ S, finiteEmbedding v (finiteProj v x) with hhdef
  refine ⟨h, ?_, htN ⟨fun w ↦ ?_, fun v ↦ ?_⟩⟩
  · exact Subgroup.mul_mem _
      (Subgroup.prod_mem _ fun w _ ↦ infiniteEmbedding_mem_localEmbeddingSubgroup _ _)
      (Subgroup.prod_mem _ fun v _ ↦ finiteEmbedding_mem_localEmbeddingSubgroup _ _)
  · have hfi : ∀ (u : HeightOneSpectrum (𝓞 K)) (a : (u.adicCompletion K)ˣ),
        infiniteProj w (finiteEmbedding u a) = 1 := fun _ _ ↦ Units.ext rfl
    have hw : infiniteProj w h = infiniteProj w x := by
      simp only [h, map_mul, map_prod, hfi, Finset.prod_const_one, mul_one]
      rw [Finset.prod_eq_single w
          (fun u _ hu ↦ infiniteProj_infiniteEmbedding_of_ne (Ne.symm hu) _)
          (fun hw ↦ (hw (Finset.mem_univ w)).elim)]
      simp
    rw [map_mul, map_inv, hw, inv_mul_cancel]
    exact hU1 w
  · have hif : ∀ (u : InfinitePlace K) (a : (u.Completion)ˣ),
        finiteProj v (infiniteEmbedding u a) = 1 := fun _ _ ↦ Units.ext rfl
    by_cases hv : v ∈ S
    · have hv' : finiteProj v h = finiteProj v x := by
        simp only [h, map_mul, map_prod, hif, Finset.prod_const_one, one_mul]
        rw [Finset.prod_eq_single_of_mem v hv
            (fun u _ hu ↦ finiteProj_finiteEmbedding_of_ne (Ne.symm hu) _)]
        simp
      rw [map_mul, map_inv, hv', inv_mul_cancel]
      exact hV1 v
    · have hv' : finiteProj v h = 1 := by
        simp only [h, map_mul, map_prod, hif, Finset.prod_const_one, one_mul]
        rw [Finset.prod_eq_one (fun u hu ↦ finiteProj_finiteEmbedding_of_ne
            (by rintro rfl; exact hv hu) _)]
      have hvS := hv
      rw [hSdef, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hvS
      rw [map_mul, map_inv, hv', inv_one, one_mul, hvS.1]
      exact hvS.2

theorem dense_localEmbeddingSubgroup : Dense (localEmbeddingSubgroup K : Set (IdeleGroup K)) := by
  refine fun x ↦ mem_closure_iff_nhds.2 fun t ht ↦ ?_
  have hN : {y : IdeleGroup K | x * y⁻¹ ∈ t} ∈ 𝓝 (1 : IdeleGroup K) := by
    have hc : Continuous fun y : IdeleGroup K ↦ x * y⁻¹ := continuous_const.mul continuous_inv
    exact hc.continuousAt.preimage_mem_nhds (by simpa using ht)
  obtain ⟨h, hh, hhN⟩ := exists_mem_localEmbeddingSubgroup_inv_mul_mem hN x
  exact ⟨h, by simpa using hhN, hh⟩

theorem continuous_monoidHom_ext {M : Type*} [Monoid M] [TopologicalSpace M] [T2Space M]
    {ψ ψ' : IdeleGroup K →* M} (hψ : Continuous ψ) (hψ' : Continuous ψ')
    (hfin : ∀ v a, ψ (finiteEmbedding v a) = ψ' (finiteEmbedding v a))
    (hinf : ∀ w a, ψ (infiniteEmbedding w a) = ψ' (infiniteEmbedding w a)) : ψ = ψ' := by
  have hle : localEmbeddingSubgroup K ≤ ψ.eqLocus ψ' :=
    sup_le (iSup_le fun v ↦ by rintro _ ⟨a, rfl⟩; exact hfin v a)
      (iSup_le fun w ↦ by rintro _ ⟨a, rfl⟩; exact hinf w a)
  exact MonoidHom.ext (congrFun (Continuous.ext_on dense_localEmbeddingSubgroup hψ hψ' fun x hx ↦ hle hx))

end IdeleGroup

namespace IdeleMap

open IdeleGroup

variable {K : Type*} [Field K] [NumberField K] {G : Type*} [CommGroup G]
  [TopologicalSpace G] [DiscreteTopology G]
  (φ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* G)
  (φinf : ∀ w : InfinitePlace K, (w.Completion)ˣ →* G)
  (hφ : ∀ᶠ v in cofinite,
    (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (φ v).ker)

theorem eq_ideleMap (hφc : ∀ v, Continuous (φ v)) (hφinfc : ∀ w, Continuous (φinf w))
    {ψ : IdeleGroup K →* G} (hψ : Continuous ψ)
    (hfin : ∀ v, ψ.comp (finiteEmbedding v) = φ v)
    (hinf : ∀ w, ψ.comp (infiniteEmbedding w) = φinf w) :
    ψ = ideleMap φ φinf hφ :=
  continuous_monoidHom_ext hψ (continuous_ideleMap φ φinf hφ hφc hφinfc)
    (fun v a ↦ by rw [ideleMap_finiteEmbedding, ← hfin v, MonoidHom.comp_apply])
    (fun w a ↦ by rw [ideleMap_infiniteEmbedding, ← hinf w, MonoidHom.comp_apply])


end IdeleMap

end

end GroundTheory.Global
end
