module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle041
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle032
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle031
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle062
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle033
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle053
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle056
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpModel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle050
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PNumericalSegre
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle024
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle010
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
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem SymmetricSpanHsymm.full : SymmetricSpanHsymm.Statement := SymmetricSpanHsymm.proof

theorem DivisorIdealCycle.full : DivisorIdealCycle.Statement.{u} := DivisorIdealCycle.proof

theorem VNumCut.full : VNumCut.Statement.{u} := VNumCut.proof CutByForm.full

theorem VertCutEff.full : VertCutEff.Statement.{u} :=
  VertCutEff.proof VNumCut.full DivisorIdealCycle.full IntNumAddFirst.full

theorem LeftExpansion.full : LeftExpansion.Statement.{u} := LeftExpansion.proof VNumCut.full

theorem RightExpansion.full : RightExpansion.Statement.{u} :=
  RightExpansion.proof VertCutEff.full DivisorIdealCycle.full

theorem ExcessPositive.full : ExcessPositive.Statement.{u} := ExcessPositive.proof

theorem AvoidingFormExists.full : AvoidingFormExists.Statement.{u} := AvoidingFormExists.proof

theorem HorizontalAvoidingForm.full : HorizontalAvoidingForm.Statement.{u} :=
  HorizontalAvoidingForm.proof

theorem LeftSideAdditiveInDegree.full : LeftSideAdditiveInDegree.Statement.{u} := LeftSideAdditiveInDegree.proof

theorem RightSideMultiplicativeInForm.full : RightSideMultiplicativeInForm.Statement.{u} :=
  RightSideMultiplicativeInForm.proof DivCycleMul.full DivCycleFiniteSupport.full

theorem CommonFactorRemoval.full : CommonFactorRemoval.Statement.{u} := CommonFactorRemoval.proof DivCycleMul.full

theorem AdditivityInDivisor.full : AdditivityInDivisor.Statement.{u} :=
  AdditivityInDivisor.proof DivCycleMul.full DivCycleFiniteSupport.full IntNumAddFirst.full
    SupSpanMultiHomog.full MinimalPrimeMultiHomog.full SpecialIdealMultiHomog.full
    SpecialIdealCorresp.full SpecialQuotDim.full DimStrictDrop.full

theorem TautologicalCase.full : TautologicalCase.Statement.{u} :=
  TautologicalCase.proof IntNumAddFirst.full MinimalPrimeMultiHomog.full SupSpanMultiHomog.full
    SpecialQuotDim.full SpecialIdealCorresp.full SpecialIdealMultiHomog.full DimStrictDrop.full

theorem FlagBundlePullbackVanish.of_open (hdim : FlagBundleDim.Statement) :
    FlagBundlePullbackVanish.Statement :=
  FlagBundlePullbackVanish.proof FieldNumbers.ProjectionFormulaContracted.full hdim

theorem FlagBundleCut.of_open (hdim : FlagBundleDim.Statement)
    (hforms : FlagBundleSectionForms.Statement) (hdiv : FlagBundleSectionDiv.Statement) :
    FlagBundleCut.Statement :=
  FlagBundleCut.proof hdim hforms hdiv FieldNumbers.CutRational.full

theorem FlagBundleLineBase.of_open (hdim : FlagBundleDim.Statement)
    (hsec : FlagLineSection.Statement) (hdeg : FlagLineDegree.Statement)
    (hloc : FieldNumbers.DivPushForwardLocal.Statement.{0}) : FlagBundleLineBase.Statement :=
  FlagBundleLineBase.proof hdim hsec hdeg
    (FieldNumbers.ProjectionFormulaDegree.of_divPushForward
      (FieldNumbers.DivPushForward.proof FieldNumbers.ContractRelDimLe.proof hloc))

theorem NumericalSegre.of_open (hdim : FlagBundleDim.Statement)
    (hforms : FlagBundleSectionForms.Statement) (hdiv : FlagBundleSectionDiv.Statement)
    (hsec : FlagLineSection.Statement) (hdeg : FlagLineDegree.Statement)
    (hloc : FieldNumbers.DivPushForwardLocal.Statement.{0}) : NumericalSegre.Statement :=
  NumericalSegre.proof FieldNumbers.IntNumAdd.full hdim (FlagBundleCut.of_open hdim hforms hdiv)
    (FlagBundlePullbackVanish.of_open hdim) (FlagBundleLineBase.of_open hdim hsec hdeg hloc)

theorem LocalCoefficient.of_open (hl : LeftTermSupport.Statement.{u})
    (hr : RightTermSupport.Statement.{u}) (hring : LocalCoeffRing.Statement.{u}) :
    LocalCoefficient.Statement.{u} :=
  LocalCoefficient.proof hl hr hring

theorem NoCommonComponentCase.of_open (hl : LeftTermSupport.Statement.{u})
    (hr : RightTermSupport.Statement.{u}) (hring : LocalCoeffRing.Statement.{u}) :
    NoCommonComponentCase.Statement.{u} :=
  NoCommonComponentCase.proof LeftExpansion.full RightExpansion.full (LocalCoefficient.of_open hl hr hring)
    IntNumVanish.full

theorem BlowUpModel.of_open (hrees : ReesAlgebraDim.Statement.{u}) : BlowUpModel.Statement.{u} :=
  BlowUpModel.proof hrees

theorem BlowUpDecomposition.of_open (hrees : ReesAlgebraDim.Statement.{u})
    (hst : BlowUpStrictTransform.Statement.{u}) : BlowUpDecomposition.Statement.{u} :=
  BlowUpDecomposition.proof (BlowUpModel.of_open hrees) hst

theorem BlowUpInvariance.of_open (hvert : BlowUpVerticalPush.Statement.{u})
    (hdiv : BlowUpDivisorPush.Statement.{u}) (hhor : BlowUpHorizontalCorresp.Statement.{u})
    (hcomp : HorizontalComponentModel.Statement.{u}) : BlowUpInvariance.Statement.{u} :=
  BlowUpInvariance.proof hvert hdiv hhor hcomp DivCycleFiniteSupport.full

theorem BlowUpReduction.of_open (hrees : ReesAlgebraDim.Statement.{u})
    (hst : BlowUpStrictTransform.Statement.{u}) (hvert : BlowUpVerticalPush.Statement.{u})
    (hdiv : BlowUpDivisorPush.Statement.{u}) (hhor : BlowUpHorizontalCorresp.Statement.{u})
    (hcomp : HorizontalComponentModel.Statement.{u}) : BlowUpReduction.Statement.{u} :=
  BlowUpReduction.proof (BlowUpDecomposition.of_open hrees hst)
    (BlowUpInvariance.of_open hvert hdiv hhor hcomp) CommonFactorRemoval.full AdditivityInDivisor.full
    RightSideMultiplicativeInForm.full LeftSideAdditiveInDegree.full TautologicalCase.full

theorem CommonFactorInduction.of_open (hrees : ReesAlgebraDim.Statement.{u})
    (hst : BlowUpStrictTransform.Statement.{u}) (hdrop : BlowUpExcessDecreases.Statement.{u})
    (hvert : BlowUpVerticalPush.Statement.{u}) (hdiv : BlowUpDivisorPush.Statement.{u})
    (hhor : BlowUpHorizontalCorresp.Statement.{u}) (hcomp : HorizontalComponentModel.Statement.{u}) :
    CommonFactorInduction.Statement.{u} :=
  CommonFactorInduction.proof ExcessPositive.full AvoidingFormExists.full HorizontalAvoidingForm.full
    (BlowUpDecomposition.of_open hrees hst) hdrop
    (BlowUpReduction.of_open hrees hst hvert hdiv hhor hcomp) LeftSideAdditiveInDegree.full RightSideMultiplicativeInForm.full
    DivCycleMul.full

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mcIdeal joinCoord fnField)

namespace JoinTwoModels

section Field

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} {ι : K → Type}

theorem ratio_mem {K' : Type} {ι' : K' → Type} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    (h : fnField O (joinCoord x z) = fnField O x) (k : K') (i j : ι' k) :
    z ⟨k, i⟩ / z ⟨k, j⟩ ∈ fnField O x := by
  rw [← h]
  exact Subfield.subset_closure (Or.inr ⟨⟨.inr k, (i, j)⟩, rfl⟩)

theorem fnField_join_two {K₁ : Type} {ι₁ : K₁ → Type} {K₂ : Type} {ι₂ : K₂ → Type} (x : (Σ k, ι k) → Ω)
    (z₁ : (Σ k, ι₁ k) → Ω) (z₂ : (Σ k, ι₂ k) → Ω) (h₁ : fnField O (joinCoord x z₁) = fnField O x)
    (h₂ : fnField O (joinCoord x z₂) = fnField O x) :
    fnField O (joinCoord x (joinCoord z₁ z₂)) = fnField O x := by
  apply le_antisymm
  · refine (Subfield.closure_le).2 ?_
    rintro _ (⟨a, rfl⟩ | ⟨⟨kk, i, j⟩, rfl⟩)
    · exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
    · rcases kk with k | k | k
      · exact Subfield.subset_closure (Or.inr ⟨⟨k, (i, j)⟩, rfl⟩)
      · exact ratio_mem x z₁ h₁ k i j
      · exact ratio_mem x z₂ h₂ k i j
  · refine (Subfield.closure_le).2 ?_
    rintro _ (⟨a, rfl⟩ | ⟨⟨k, i, j⟩, rfl⟩)
    · exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
    · exact Subfield.subset_closure (Or.inr ⟨⟨.inl k, (i, j)⟩, rfl⟩)

end Field

section Model

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω] [Algebra O Ω]

theorem exists_ne_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω)
    {d : ℕ} (h : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O y) d) (k : K) : ∃ i, y ⟨k, i⟩ ≠ 0 := by
  classical
  rw [BundleExamples.mcIdeal_eq_pointIdeal, BundleExamples.isModelOver_iff] at h
  obtain ⟨j, hj⟩ := h.2.multiProj.relevant k
  refine ⟨j, fun h0 => hj ?_⟩
  rw [pointIdeal, RingHom.mem_ker]
  simp [pointConeMap, h0]

end Model

end JoinTwoModels


open JoinTwoModels in
theorem JoinTwoModels.proof (hC : ConeTrdegFnField.Statement) : JoinTwoModels.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d hx K₁ _ ι₁ _ z₁ K₂ _ ι₂ _ z₂ h₁ hf₁ h₂ hf₂
  classical
  have hf := fnField_join_two x z₁ z₂ hf₁ hf₂
  refine ⟨?_, hf⟩
  have hy : ∀ k, ∃ i, joinCoord x (joinCoord z₁ z₂) ⟨k, i⟩ ≠ 0 := by
    rintro (k | k | k)
    · exact exists_ne_zero x hx k
    · exact exists_ne_zero _ h₁ (.inr k)
    · exact exists_ne_zero _ h₂ (.inr k)
  have hx' : ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0 := exists_ne_zero x hx
  have hxW := hx
  rw [BundleExamples.mcIdeal_eq_pointIdeal, BundleExamples.isModelOver_iff] at hxW
  obtain ⟨hK, hW⟩ := hxW
  have hinj : Function.Injective (algebraMap O Ω) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have hmem : a ∈ (pointIdeal O x).comap (C : O →+* MRing ι O) := by
      simp only [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C,
        MvPolynomial.algebraMap_apply, ha, map_zero]
    rw [hW.noTorsion] at hmem
    exact hmem
  rw [BundleExamples.mcIdeal_eq_pointIdeal, BundleExamples.isModelOver_iff]
  have hP := GenericProjClosureDim.isMultiProjPrime_pointIdeal (R := O) _ hy
  have hPC : (pointIdeal O (joinCoord x (joinCoord z₁ z₂))).comap
      (C : O →+* MRing (Sum.elim ι (Sum.elim ι₁ ι₂)) O) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [← hW.noTorsion]
    simp only [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C,
      MvPolynomial.algebraMap_apply, C_eq_zero] at ha ⊢
    exact ha
  refine ⟨inferInstance, ⟨hP, hPC, ?_⟩⟩

  have hdW := DvrConeDimTrdeg.proof O K ι (pointIdeal O x) hW.multiProj hW.noTorsion
  have hdJ := DvrConeDimTrdeg.proof O (K ⊕ (K₁ ⊕ K₂)) (Sum.elim ι (Sum.elim ι₁ ι₂)) _ hP hPC
  have htW := hC O Ω hinj K ι x hx'
  have htJ := hC O Ω hinj (K ⊕ (K₁ ⊕ K₂)) (Sum.elim ι (Sum.elim ι₁ ι₂)) _ hy
  rw [hf] at htJ
  rw [BundleExamples.mcIdeal_eq_pointIdeal] at htW htJ
  set T := Algebra.trdeg O (Algebra.adjoin O (fnField O x : Set Ω))
  rw [hW.dim] at hdW
  erw [htW] at hdW
  erw [hdJ, htJ]
  rw [map_add (f := _), map_natCast] at hdW ⊢
  have hT : Cardinal.toENat T = d := by
    have h1 : ((Cardinal.toENat T + (Fintype.card K : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) =
        ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdW.symm
    have h2 : Cardinal.toENat T + ((Fintype.card K + 1 : ℕ) : ℕ∞) = (d : ℕ∞) + ((Fintype.card K + 1 : ℕ) : ℕ∞) := by
      have := WithBot.coe_injective h1
      push_cast at this ⊢
      rw [← add_assoc, this]; ring
    exact (WithTop.add_right_cancel (ENat.natCast_ne_top _) h2)
  rw [hT, Fintype.card_sum, Fintype.card_sum]
  have e : ((d : ℕ∞) + ((Fintype.card K + (Fintype.card K₁ + Fintype.card K₂) : ℕ) : ℕ∞) + 1) =
      ((d + 1 + (Fintype.card K + (Fintype.card K₁ + Fintype.card K₂)) : ℕ) : ℕ∞) := by
    push_cast; ring
  rw [e]
  norm_cast

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem comap_C_pointIdeal {R : Type*} [CommRing R] {Φ : Type*} [Field Φ] [Algebra R Φ] {K : Type*}
    {ι : K → Type*} (h : Function.Injective (algebraMap R Φ)) (pt : (Σ k, ι k) → Φ) :
    (pointIdeal R pt).comap (C : R →+* MvPolynomial (Σ k, ι k) R) = ⊥ := by
  ext a
  simp only [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C,
    MvPolynomial.algebraMap_apply, C_eq_zero, Submodule.mem_bot]
  exact ⟨fun ha => h (by rw [ha, map_zero]), fun ha => by rw [ha, map_zero]⟩

theorem specialIdeal_dim_add_one_le {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {K : Type*} {ι : K → Type*} (P : Ideal (MvPolynomial (Σ k, ι k) O)) [P.IsPrime]
    (hPC : P.comap (C : O →+* MvPolynomial (Σ k, ι k) O) = ⊥) :
    ringKrullDim (MvPolynomial (Σ k, ι k) (IsLocalRing.ResidueField O) ⧸
        P.map (MvPolynomial.map (IsLocalRing.residue O))) + 1 ≤
      ringKrullDim (MvPolynomial (Σ k, ι k) O ⧸ P) := by
  set φ : MvPolynomial (Σ k, ι k) O →+* MvPolynomial (Σ k, ι k) (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O) with hφdef
  have hφ : Function.Surjective φ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker φ = Ideal.span {(C ϖ : MvPolynomial (Σ k, ι k) O)} := by
    rw [hφdef, MvPolynomial.ker_map, IsLocalRing.ker_residue, hϖ.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton]
  set g := (Ideal.Quotient.mk (P.map φ)).comp φ with hgdef
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hφ
  have hkg : RingHom.ker g = P ⊔ Ideal.span {(C ϖ : MvPolynomial (Σ k, ι k) O)} := by
    rw [hgdef, ← RingHom.comap_ker, Ideal.mk_ker, Ideal.comap_map_of_surjective _ hφ,
      ← RingHom.ker_eq_comap_bot, hker]
  have e1 := (Ideal.quotEquivOfEq hkg.symm).trans (RingHom.quotientKerEquivOfSurjective hg)
  set r : MvPolynomial (Σ k, ι k) O ⧸ P := Ideal.Quotient.mk P (C ϖ) with hrdef
  have hspan : (Ideal.span {(C ϖ : MvPolynomial (Σ k, ι k) O)}).map (Ideal.Quotient.mk P) = Ideal.span {r} := by
    rw [Ideal.map_span, Set.image_singleton]
  have e2 := (Ideal.quotEquivOfEq hspan.symm).trans (DoubleQuot.quotQuotEquivQuotSup P
    (Ideal.span {(C ϖ : MvPolynomial (Σ k, ι k) O)}))
  have hr0 : r ≠ 0 := by
    intro h0
    rw [hrdef, Ideal.Quotient.eq_zero_iff_mem] at h0
    have hmem : ϖ ∈ P.comap (C : O →+* MvPolynomial (Σ k, ι k) O) := h0
    rw [hPC, Ideal.mem_bot] at hmem
    exact hϖ.ne_zero hmem
  have hle := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hr0)
  rwa [ringKrullDim_eq_of_ringEquiv e2, ringKrullDim_eq_of_ringEquiv e1] at hle

theorem relDim_specialIdeal_lt {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} (P : Ideal (MRing ι O)) [P.IsPrime]
    (hPC : P.comap (C : O →+* MRing ι O) = ⊥) (n : ℕ)
    (hdim : ringKrullDim (MRing ι O ⧸ P) ≤ ((n + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    FieldNumbers.relDim (specialIdeal P) < ((n : ℕ) : WithBot (WithTop ℤ)) := by
  have h := (specialIdeal_dim_add_one_le hϖ P hPC).trans hdim
  unfold FieldNumbers.relDim specialIdeal
  generalize ringKrullDim (MvPolynomial (Σ k, ι k) (IsLocalRing.ResidueField O) ⧸
    P.map (MvPolynomial.map (IsLocalRing.residue O))) = a at h ⊢
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ ((n + Fintype.card K : ℕ) : ℕ∞) := by exact_mod_cast h
      simp at h'
    | coe m =>
      have h' : ((m + 1 : ℕ) : ℕ∞) ≤ ((n + Fintype.card K : ℕ) : ℕ∞) := by exact_mod_cast h
      have h'' : m + 1 ≤ n + Fintype.card K := by exact_mod_cast h'
      have hlt : (m : ℤ) - Fintype.card K < n := by omega
      change (((((m : ℤ) - Fintype.card K : ℤ) : WithTop ℤ)) : WithBot (WithTop ℤ)) < (((n : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
      exact_mod_cast hlt

theorem SegreFlagProjSpecialDim.proof (hDim : PrimeDimLeTrdeg.Statement) (hTr : FlagProjTrdegLe.Statement) :
    SegreFlagProjSpecialDim.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hBB' w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _
    e t ht k hk
  obtain ⟨h1, h2⟩ := hTr O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk

  have hVt : (Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y)).toENat = ((d + Fintype.card K : ℕ) : ℕ∞) := by
    have h := DvrConeDimTrdeg.proof O K ι _ hV.multiProj hV.noTorsion
    rw [hV.dim] at h
    have h0 : ((d + 1 + Fintype.card K : ℕ) : ℕ∞) = (Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y)).toENat + 1 := by
      exact_mod_cast h
    have h' : ((d + Fintype.card K : ℕ) : ℕ∞) + 1 = (Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y)).toENat + 1 := by
      rw [← h0]; push_cast; ring
    exact (WithTop.add_right_cancel ENat.one_ne_top h').symm

  have hOΩ : Function.Injective (algebraMap O Ω) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have hmem : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := by
      simp [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, ha]
    rwa [hV.noTorsion, Ideal.mem_bot] at hmem
  have hOΦ : Function.Injective (algebraMap O Φ) := by
    rw [IsScalarTower.algebraMap_eq O Ω Φ]
    exact (algebraMap Ω Φ).injective.comp hOΩ

  have key : ∀ {K' : Type} [Fintype K'] [DecidableEq K'] (j : K' ↪ Option (Option K)), Fintype.card K' = Fintype.card K + 1 →
      Algebra.trdeg O (MRing (fun o => bundleIdx (bundleIdx ι M) M' (j o)) O ⧸
          pointIdeal O (flagProjPt j y w e φ φ' t k)) ≤ Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) + (k : Cardinal) →
      FieldNumbers.relDim (specialIdeal (pointIdeal O (flagProjPt j y w e φ φ' t k))) <
        ((d + k : ℕ) : WithBot (WithTop ℤ)) := by
    intro K' _ _ j hcard hle
    have hP : (pointIdeal O (flagProjPt j y w e φ φ' t k)).IsPrime := by
      unfold pointIdeal
      exact RingHom.ker_isPrime _
    have hPC := comap_C_pointIdeal hOΦ (flagProjPt j y w e φ φ' t k)
    refine relDim_specialIdeal_lt hϖ _ hPC (d + k) ((hDim O K' _ _ hP hPC).trans ?_)
    have ht : Cardinal.toENat _ ≤ Cardinal.toENat _ := OrderHomClass.mono Cardinal.toENat hle
    simp only [map_add (f := _), map_natCast, hVt] at ht
    have : ((Algebra.trdeg O (MRing (fun o => bundleIdx (bundleIdx ι M) M' (j o)) O ⧸
        pointIdeal O (flagProjPt j y w e φ φ' t k))).toENat + 1 : ℕ∞) ≤ ((d + k + Fintype.card K' : ℕ) : ℕ∞) := by
      rw [hcard]
      calc _ ≤ ((d + Fintype.card K : ℕ) : ℕ∞) + (k : ℕ∞) + 1 := by gcongr
        _ = _ := by push_cast; ring
    exact_mod_cast this
  exact ⟨key Function.Embedding.some (by simp) h1, key secondFactorBlocks (by simp) h2⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
