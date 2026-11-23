module

public import GroundTheory.ProfiniteCohomology.RealPlaces.OrderTwoTate
public import GroundTheory.ProfiniteCohomology.RealPlaces.Bundle002
public import GroundTheory.ProfiniteCohomology.Bundle006
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain GroundTheory.Global

universe u

noncomputable section

section Restrict

variable {F L Ω : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] [IsGalois F Ω]
  {S : Set (HeightOneSpectrum (𝓞 F))}
  (hL : ∀ x : L, algebraMap L Ω x ∈ maxUnramifiedOutside F Ω S) [Normal F L]

def gsRestrictGal : galUnramifiedOutside F Ω S →* (L ≃ₐ[F] L) :=
  letI : Algebra L (maxUnramifiedOutside F Ω S) := (gsEmbedding hL).toRingHom.toAlgebra
  haveI : IsScalarTower F L (maxUnramifiedOutside F Ω S) :=
    IsScalarTower.of_algebraMap_eq fun a => ((gsEmbedding hL).commutes a).symm
  AlgEquiv.restrictNormalHom L

theorem gsEmbedding_gsRestrictGal (σ : galUnramifiedOutside F Ω S) (l : L) :
    gsEmbedding hL (gsRestrictGal hL σ l) = σ (gsEmbedding hL l) := by
  let _ : Algebra L (maxUnramifiedOutside F Ω S) := (gsEmbedding hL).toRingHom.toAlgebra
  have : IsScalarTower F L (maxUnramifiedOutside F Ω S) :=
    IsScalarTower.of_algebraMap_eq fun a => ((gsEmbedding hL).commutes a).symm
  exact AlgEquiv.restrictNormal_commutes σ L l

theorem gsRestrictGal_eq_iff (σ : galUnramifiedOutside F Ω S) (τ : L ≃ₐ[F] L) :
    gsRestrictGal hL σ = τ ↔ ∀ l : L, σ (gsEmbedding hL l) = gsEmbedding hL (τ l) := by
  constructor
  · rintro rfl l
    exact (gsEmbedding_gsRestrictGal hL σ l).symm
  · intro h
    ext l
    exact (gsEmbedding hL).injective ((gsEmbedding_gsRestrictGal hL σ l).trans (h l))

theorem gsRestrictGal_eq_one_iff (σ : galUnramifiedOutside F Ω S) :
    gsRestrictGal hL σ = 1 ↔ σ ∈ gsOpenSubgroup S hL := by
  rw [gsRestrictGal_eq_iff, mem_gsOpenSubgroup_iff]
  rfl

theorem ker_gsRestrictGal :
    (gsRestrictGal hL).ker = (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)) :=
  Subgroup.ext fun σ => (MonoidHom.mem_ker).trans (gsRestrictGal_eq_one_iff hL σ)

theorem gsOpenSubgroup_normal :
    (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)).Normal := by
  rw [← ker_gsRestrictGal hL]
  exact MonoidHom.normal_ker _

theorem gsRestrictGal_surjective : Function.Surjective (gsRestrictGal hL) := by
  let _ : Algebra L (maxUnramifiedOutside F Ω S) := (gsEmbedding hL).toRingHom.toAlgebra
  have : IsScalarTower F L (maxUnramifiedOutside F Ω S) :=
    IsScalarTower.of_algebraMap_eq fun a => ((gsEmbedding hL).commutes a).symm
  exact AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := L) (maxUnramifiedOutside F Ω S)

def gsQuotientGalEquiv [(gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)).Normal] :
    galUnramifiedOutside F Ω S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)) ≃*
      (L ≃ₐ[F] L) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_gsRestrictGal hL).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (gsRestrictGal_surjective hL))

@[simp]
theorem gsQuotientGalEquiv_mk
    [(gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)).Normal]
    (σ : galUnramifiedOutside F Ω S) :
    gsQuotientGalEquiv hL (QuotientGroup.mk σ) = gsRestrictGal hL σ :=
  rfl

variable (ιs : ∀ v : S, Ω →ₐ[F] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F))

def gsDecompGroup (v : S) : Subgroup (L ≃ₐ[F] L) :=
  ((gsRestrictGal hL).comp (gsFinFamily S ιs v).toMonoidHom).range

theorem map_range_gsQuotientGalEquiv
    [(gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)).Normal] (v : S) :
    ((QuotientGroup.mk' (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S))).comp
        (gsFinFamily S ιs v).toMonoidHom).range.map (gsQuotientGalEquiv hL).toMonoidHom =
      gsDecompGroup hL ιs v := by
  rw [MonoidHom.map_range]
  rfl

end Restrict

section Real

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  {L : FiniteSubfield} [Fact (K ≤ L)] [Normal K.1 L.1]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)

def gsRealDecompGroup (v : {v : InfinitePlace K.1 // v.IsReal}) : Subgroup (L.1 ≃ₐ[K.1] L.1) :=
  ((gsRestrictGal hL).comp (gsRealFamily S ιr v).toMonoidHom).range

end Real

end

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))

section Places

variable (ι : ∀ v : InfinitePlace K.1, ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion)

def gsInfFamily (v : InfinitePlace K.1) :
    Gal(AlgebraicClosure v.Completion / v.Completion) →ₜ* galUnramifiedOutside K.1 ℚ̄ S :=
  ⟨decompHomS v.Completion S (ι v), continuous_decompHomS (Kv := v.Completion) S (ι v)⟩

end Places

section Factor

variable (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M]

def gsRealH0Card
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (v : {v : InfinitePlace K.1 // v.IsReal}) : ℕ :=
  Nat.card (cohomology (Rep.res (gsRealFamily S ιr v).toMonoidHom M) 0)


open scoped Classical in
def gsEulerRatio
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion) : ℚ :=
  eulerChar M * (Nat.card M : ℚ) ^ Fintype.card (InfinitePlace K.1) /
    ∏ v : {v : InfinitePlace K.1 // v.IsReal}, (gsRealH0Card S M ιr v : ℚ)

end Factor

section Statement


end Statement

end

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

namespace Involution

variable {M : Type*} [AddCommGroup M] {σ : M →+ M}

theorem ker_id_add_eq_fixedSub_neg : (AddMonoidHom.id M + σ).ker = fixedSub (-σ) := by
  ext x
  rw [AddMonoidHom.mem_ker, mem_fixedSub, AddMonoidHom.add_apply, AddMonoidHom.id_apply,
    AddMonoidHom.neg_apply, neg_eq_iff_eq_neg, eq_neg_iff_add_eq_zero, add_comm]

theorem card_tateQuot_mul_card (hσ : ∀ x, σ (σ x) = x) :
    Nat.card (tateQuot σ) * Nat.card M = Nat.card (fixedSub σ) * Nat.card (fixedSub (-σ)) := by
  have h1 : Nat.card (fixedSub σ) =
      Nat.card (tateQuot σ) * Nat.card (traceSub σ) := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
      ((traceSub σ).addSubgroupOf (fixedSub σ)),
      Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (traceSub_le_fixedSub hσ)).toEquiv]
  have h2 : Nat.card (traceSub σ) * Nat.card (fixedSub (-σ)) = Nat.card M := by
    rw [← ker_id_add_eq_fixedSub_neg, traceSub]
    rw [← AddSubgroup.index_ker, mul_comm, AddSubgroup.card_mul_index]
  rw [h1, mul_assoc, h2]

variable [Finite M]

theorem card_tateQuot_neg (hσ : ∀ x, σ (σ x) = x) :
    Nat.card (tateQuot (-σ)) = Nat.card (tateQuot σ) := by
  have hσ' : ∀ x, (-σ) ((-σ) x) = x := fun x => by
    rw [AddMonoidHom.neg_apply, AddMonoidHom.neg_apply, map_neg, neg_neg, hσ]
  have e1 := card_tateQuot_mul_card hσ
  have e2 := card_tateQuot_mul_card hσ'
  rw [neg_neg, mul_comm (Nat.card (fixedSub (-σ)))] at e2
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (e2.trans e1.symm)

end Involution

namespace OrderTwo

section Card

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DiscreteTopology G] (A : Rep.{0} k G) [IsDiscreteRep A] {c : G}
  (hG : ∀ g : G, g = 1 ∨ g = c) (hc : c ≠ 1)


omit [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G] [IsDiscreteRep A] in
include hG hc in
theorem act_act (x : A) : act A c (act A c x) = x := by
  change A.ρ c (A.ρ c x) = x
  rw [← Module.End.mul_apply, ← map_mul, mul_self_eq_one hG hc, map_one, Module.End.one_apply]

variable [Finite A]


include hG hc in
theorem finite_cohomology_one : Finite (cohomology A 1) :=
  Finite.of_equiv _ (h1EquivOfOrderTwo A hG hc).toEquiv


include hG hc in
theorem finite_cohomology_two : Finite (cohomology A 2) :=
  Finite.of_equiv _ (h2EquivOfOrderTwo A hG hc).toEquiv


include hG hc in
theorem card_cohomology_one_eq_two : Nat.card (cohomology A 1) = Nat.card (cohomology A 2) := by
  rw [← Nat.card_congr (h1EquivOfOrderTwo A hG hc).toEquiv, ← Nat.card_congr (h2EquivOfOrderTwo A hG hc).toEquiv]
  exact Involution.card_tateQuot_neg (act_act A hG hc)


include hG hc in
theorem eulerChar_eq_card_cohomology_zero : eulerChar A = Nat.card (cohomology A 0) := by
  have := finite_cohomology_one A hG hc
  have h1 : (Nat.card (cohomology A 1) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := cohomology A 1)).ne'
  rw [eulerChar, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_one,
    ← card_cohomology_one_eq_two A hG hc]
  norm_num
  field_simp

end Card

end OrderTwo

section RealPlace

open NumberField GroundTheory.Global

variable {K : FiniteSubfield} (v : InfinitePlace K.1) (hv : v.IsReal)
  (M : Rep.{0} (ULift.{0} ℤ) Gal(AlgebraicClosure v.Completion / v.Completion)) [IsDiscreteRep M]
  [Finite M]



include hv in
theorem eulerChar_eq_card_cohomology_zero_of_isReal :
    eulerChar M = Nat.card (cohomology M 0) :=
  OrderTwo.eulerChar_eq_card_cohomology_zero M (eq_one_or_eq_realConj v hv) (realConj_ne_one v hv)


include hv in
theorem finite_cohomology_of_isReal (n : ℕ) (hn : n ≤ 2) : Finite (cohomology M n) := by
  interval_cases n
  · exact Finite.of_equiv _ (H0Iso M).toLinearEquiv.toEquiv.symm
  · exact OrderTwo.finite_cohomology_one M (eq_one_or_eq_realConj v hv) (realConj_ne_one v hv)
  · exact OrderTwo.finite_cohomology_two M (eq_one_or_eq_realConj v hv) (realConj_ne_one v hv)

end RealPlace

section GS

open NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
  (v : {v : InfinitePlace K.1 // v.IsReal})

theorem gsReal_eulerChar_eq_card_cohomology_zero :
    eulerChar (Rep.res (gsRealFamily S ιr v).toMonoidHom M) =
      Nat.card (cohomology (Rep.res (gsRealFamily S ιr v).toMonoidHom M) 0) :=
  eulerChar_eq_card_cohomology_zero_of_isReal v.1 v.2 _

theorem gsReal_finite_cohomology (n : ℕ) (hn : n ≤ 2) :
    Finite (cohomology (Rep.res (gsRealFamily S ιr v).toMonoidHom M) n) :=
  finite_cohomology_of_isReal v.1 v.2 _ n hn

end GS

end GroundTheory.ProfCoh
end
