module

import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCriticalImageNull
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle073
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeMassOfFibre
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.SetTheory.ZFC.PSet
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartNormAlgClosed

section Chart

variable {F : Type} [Field F] {n e : ℕ} (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F)
  (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime]

theorem algebraMap_tower (x : MvPolynomial (Fin e × Fin n) F) :
    algebraMap (Localization.AtPrime p) (ChartLoc I t e p) (algebraMap _ _ x) =
      algebraMap (ChartInc I t e) (ChartLoc I t e p) (algebraMap _ (ChartInc I t e) x) := by
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem chartX_C (c : F) :
    chartX I t e (C c) = algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (C c) := by
  show Ideal.Quotient.mk _ (rename Sum.inl (C c)) = Ideal.Quotient.mk _ (rename Sum.inr (C c))
  simp only [rename_C]

theorem algebraMap_localization_C (c : F) :
    algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p) (C c) =
      algebraMap F (Localization.AtPrime p) c := by
  rw [IsScalarTower.algebraMap_apply F (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p),
    MvPolynomial.algebraMap_eq]

theorem chartLin_eq_sum (u : Fin n → F) :
    algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u) =
      ∑ m, algebraMap F (Localization.AtPrime p) (u m) •
        algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m)) := by

  simp only [chartLin, linForm, map_sum, map_mul, Algebra.smul_def]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← algebraMap_localization_C p, algebraMap_tower, chartX_C]

theorem chartLin_self : chartLin I t e t = 1 := by
  have h : chartX I t e (linForm t - 1) = 0 := by
    exact (Ideal.Quotient.eq_zero_iff_mem (I := chartIncIdeal I t e)).mpr
      (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))))
  rw [map_sub, map_one, sub_eq_zero] at h
  exact h

theorem adjoin_eq_top :
    Algebra.adjoin (Localization.AtPrime p)
        (Set.range fun m => algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m))) = ⊤ := by
  set A := Algebra.adjoin (Localization.AtPrime p)
    (Set.range fun m => algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m)))
  have hS : ∀ x : MvPolynomial (Fin e × Fin n) F,
      algebraMap (ChartInc I t e) (ChartLoc I t e p) (algebraMap _ (ChartInc I t e) x) ∈ A := by
    intro x
    rw [← algebraMap_tower]
    exact Subalgebra.algebraMap_mem A _
  let π : MvPolynomial (Fin n ⊕ Fin e × Fin n) F →+* ChartInc I t e := Ideal.Quotient.mk (chartIncIdeal I t e)
  have hSig : ∀ y : MvPolynomial (Fin n ⊕ Fin e × Fin n) F,
      algebraMap (ChartInc I t e) (ChartLoc I t e p) (π y) ∈ A := by
    intro y
    induction y using MvPolynomial.induction_on with
    | C a =>
      have h : π (C a) = algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (C a) := by
        show _ = Ideal.Quotient.mk _ (rename Sum.inr (C a))
        rw [rename_C]
        rfl
      rw [h]
      exact hS _
    | add a b ha hb =>
      rw [map_add (f := _), map_add (f := _)]
      exact add_mem ha hb
    | mul_X a v ha =>
      rw [map_mul, map_mul]
      refine mul_mem ha ?_
      rcases v with m | im
      · refine Algebra.subset_adjoin ⟨m, ?_⟩
        show algebraMap (ChartInc I t e) (ChartLoc I t e p)
          ((Ideal.Quotient.mk (chartIncIdeal I t e) (rename Sum.inl (X m)) : ChartInc I t e)) = _
        rw [rename_X]
        rfl
      · have h : π (X (Sum.inr im)) = algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (X im) := by
          show _ = Ideal.Quotient.mk _ (rename Sum.inr (X im))
          rw [rename_X]
          rfl
        rw [h]
        exact hS _
  rw [eq_top_iff]
  intro z _
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Algebra.algebraMapSubmonoid (ChartInc I t e) p.primeCompl) z
  obtain ⟨s₀, hs₀, hs⟩ := s.2
  obtain ⟨y, rfl⟩ : ∃ y, π y = x := Ideal.Quotient.mk_surjective x
  set w := algebraMap (Localization.AtPrime p) (ChartLoc I t e p)
    (IsLocalization.mk' (Localization.AtPrime p) (1 : MvPolynomial (Fin e × Fin n) F) ⟨s₀, hs₀⟩)
  have hw : algebraMap (ChartInc I t e) (ChartLoc I t e p) (s : ChartInc I t e) * w = 1 := by
    rw [← hs, ← algebraMap_tower, ← map_mul, IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one,
      IsLocalization.mk'_self, map_one]
  have hz : IsLocalization.mk' (ChartLoc I t e p) (π y) s =
      algebraMap (ChartInc I t e) (ChartLoc I t e p) (π y) * w := by
    rw [IsLocalization.mk'_eq_iff_eq_mul, mul_assoc, mul_comm w, hw, mul_one]
  show IsLocalization.mk' (ChartLoc I t e p) (π y) s ∈ A
  rw [hz]
  exact mul_mem (hSig y) (Subalgebra.algebraMap_mem A _)

end Chart

theorem eval_map_firstGroup {F : Type} [Field F] {n e : ℕ} (p : Ideal (MvPolynomial (Fin e × Fin n) F))
    [p.IsPrime] (f : MvPolynomial (Fin (e + 1) × Fin n) F) (u : Fin n → F) :
    eval (fun m => algebraMap F (Localization.AtPrime p) (u m))
        (map (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) (firstGroup f)) =
      algebraMap _ (Localization.AtPrime p) (specFirst f u) := by
  apply _root_.GroundTheory.Heights₂.Heights.eval_map_firstGroup <;> assumption

end ChartNormAlgClosed


open ChartNormAlgClosed in
theorem ChartNormAlgClosed.proof (h₁ : IncIdealBelow.Statement) (h₂ : SpecFirstMemIncIdeal.Statement)
    (h₃ : LocalizationPrimeDVR.Statement) (h₄ : ChartFinite.Statement) (h₅ : ChartLocDomain.Statement)
    (h₆ : ChartFirstGroupPrime.Statement) (h₇ : ChartFirstGroupDvd.Statement)
    (h₈ : NormOfDividedFormSep.Statement) (h₉ : ChartFracSeparable.Statement) :
    ChartNormAlgClosed.Statement := by
  intro F _ _ n e I f t p _ hI hf hp hft u
  have htI : linForm t ∉ I := by
    intro h
    have hmem := h₂ F n e I I f t hf le_rfl h
    rw [h₁ F n e I f hI hf, Ideal.mem_bot] at hmem
    exact hft (hmem ▸ p.zero_mem)
  obtain ⟨hdom, hinj, -⟩ := h₅ F n e I f t p hI hf htI
  have : Module.Finite (Localization.AtPrime p) (ChartLoc I t e p) := h₄ F n e I f t p hI hf hft
  have : IsPrincipalIdealRing (Localization.AtPrime p) := by
    rcases hp with rfl | ⟨q, hq, rfl⟩
    · have hfield : IsField (Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin e × Fin n) F))) := by
        rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal,
          Ideal.map_bot]
      let := hfield.toField
      infer_instance
    · have := h₃ _ q _ hq rfl
      infer_instance
  have : Module.IsTorsionFree (Localization.AtPrime p) (ChartLoc I t e p) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact hinj
  have : Module.Free (Localization.AtPrime p) (ChartLoc I t e p) := Module.free_of_finite_type_torsion_free'
  have hsum : ∑ m, algebraMap F (Localization.AtPrime p) (t m) •
      algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m)) = 1 := by
    rw [← chartLin_eq_sum, chartLin_self, map_one]
  have hcomp : (algebraMap (ChartInc I t e) (ChartLoc I t e p)).comp
      (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) =
      (algebraMap (Localization.AtPrime p) (ChartLoc I t e p)).comp
        (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) :=
    RingHom.ext fun x => (algebraMap_tower I t p x).symm
  have hdvd := map_dvd (MvPolynomial.map (algebraMap (ChartInc I t e) (ChartLoc I t e p)))
    (h₇ F n e I f t hI hf htI)

  simp only [map_sum, map_mul, map_X, map_C, map_map, hcomp] at hdvd
  rw [← map_map] at hdvd
  have : Infinite F := IsAlgClosed.instInfinite
  have : Infinite (Localization.AtPrime p) :=
    Infinite.of_injective _ (algebraMap F (Localization.AtPrime p)).injective
  have key := h₈ (Localization.AtPrime p) (ChartLoc I t e p) n _ _ _ ?sep (adjoin_eq_top I t p) hsum
    (h₆ F n e I f p hI hf) hdvd (fun m => algebraMap F (Localization.AtPrime p) (u m))
  case sep =>
    let _ := FractionRing.liftAlgebra (Localization.AtPrime p) (FractionRing (ChartLoc I t e p))
    exact @h₉ F _ _ n e I f t p _ _ _ _ _ OreLocalization.instAlgebra Localization.isLocalization _ Localization.isLocalization _ _
      (FractionRing.isScalarTower_liftAlgebra _ _) _ hI hf htI
  rw [eval_map_firstGroup, eval_map_firstGroup, ← chartLin_eq_sum] at key
  exact key

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Cardinal

noncomputable section

theorem ChartFreeParAlgIndep.proof (h : ChartParAlgebraic.Statement) : ChartFreeParAlgIndep.Statement := by
  intro F _ n e K L _ _ _ _ _ _ u t η hu hK hL hrel hchart j₀ hj₀ htr
  have halg := h F n e K L u t η hK hL hrel hchart j₀ hj₀
  set A₀ := Algebra.adjoin F (Set.range fun m => η m * (η j₀)⁻¹) with hA₀
  set w : Fin e × {j : Fin n // j ≠ j₀} → L := fun p => algebraMap K L (u (p.1, p.2.1)) with hw

  have hinj : Function.Injective (Sum.elim (fun i : Fin e => ((i, j₀) : Fin e × Fin n))
      (fun p : Fin e × {j : Fin n // j ≠ j₀} => ((p.1, p.2.1) : Fin e × Fin n))) := by
    rintro (i | ⟨i, j, hj⟩) (i' | ⟨i', j', hj'⟩) hij <;>
      simp only [Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq,
        reduceCtorEq, Subtype.mk.injEq] at hij ⊢
    · exact hij.1
    · exact absurd hij.2.symm hj'
    · exact absurd hij.2 hj
    · exact hij
  have hcount : (e : Cardinal) + #(Fin e × {j : Fin n // j ≠ j₀}) ≤ #(Fin e × Fin n) := by
    calc (e : Cardinal) + #(Fin e × {j : Fin n // j ≠ j₀})
        = #(Fin e ⊕ (Fin e × {j : Fin n // j ≠ j₀})) := by simp
      _ ≤ #(Fin e × Fin n) := Cardinal.mk_le_of_injective hinj
  have huL : AlgebraicIndependent F (fun q => algebraMap K L (u q)) :=
    hu.map' (f := IsScalarTower.toAlgHom F K L) (algebraMap K L).injective
  have hK_le : (e : Cardinal) + #(Fin e × {j : Fin n // j ≠ j₀}) ≤ Algebra.trdeg F K :=
    hcount.trans hu.cardinalMk_le_trdeg
  have hL_le : (e : Cardinal) + #(Fin e × {j : Fin n // j ≠ j₀}) ≤ Algebra.trdeg F L :=
    hcount.trans huL.cardinalMk_le_trdeg

  have hind : AlgebraicIndependent A₀ w :=
    Vertical.FreeParAlgIndep.algebraicIndependent_of_trdeg A₀ w htr hL_le
  refine ⟨IntermediateField.algebraicIndependent_adjoin_iff.2 hind, ?_⟩
  have hbasis : IsTranscendenceBasis A₀ w := hind.isTranscendenceBasis_iff_isAlgebraic.2 halg
  have : FaithfulSMul F A₀ :=
    (faithfulSMul_iff_algebraMap_injective F A₀).2 (algebraMap F A₀).injective
  have : FaithfulSMul A₀ L :=
    (faithfulSMul_iff_algebraMap_injective A₀ L).2 Subtype.val_injective
  have : FaithfulSMul F K :=
    (faithfulSMul_iff_algebraMap_injective F K).2 (algebraMap F K).injective
  have : FaithfulSMul K L :=
    (faithfulSMul_iff_algebraMap_injective K L).2 (algebraMap K L).injective
  have hA₀L := trdeg_add_eq F A₀ (A := L)
  have hKL := trdeg_add_eq F K (A := L)
  rw [← hbasis.cardinalMk_eq_trdeg] at hA₀L

  have hup : Algebra.trdeg F L ≤ (e : Cardinal) + #(Fin e × {j : Fin n // j ≠ j₀}) := by
    rw [← hA₀L]
    gcongr
  have hfin : (e : Cardinal) + #(Fin e × {j : Fin n // j ≠ j₀}) < ℵ₀ :=
    Cardinal.add_lt_aleph0 (Cardinal.natCast_lt_aleph0) (Cardinal.lt_aleph0_of_finite _)
  have h0 : Algebra.trdeg K L + ((e : Cardinal) + #(Fin e × {j : Fin n // j ≠ j₀})) ≤
      0 + ((e : Cardinal) + #(Fin e × {j : Fin n // j ≠ j₀})) := by
    rw [zero_add, add_comm]
    calc (e : Cardinal) + #(Fin e × {j : Fin n // j ≠ j₀}) + Algebra.trdeg K L
        ≤ Algebra.trdeg F K + Algebra.trdeg K L := by gcongr
      _ = Algebra.trdeg F L := hKL
      _ ≤ _ := hup
  have hz : Algebra.trdeg K L = 0 :=
    nonpos_iff_eq_zero.1 ((Cardinal.add_le_add_iff_of_lt_aleph0 hfin).1 h0)
  exact trdeg_eq_zero_iff.1 hz

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem SphereMeanLinear.full : SphereMeanLinear.Statement := sphereMeanLinear

theorem ChowHeightMul.full : ChowHeightMul.Statement := chowHeightMul_of_mahlerMul mahlerMul

theorem ChowHeightRecursion.of_leaves (hV : ChowFormSectionVertical.Statement)
    (hA : MahlerSection.Statement) (hB : ChowFormBaseChange.Statement)
    (hAv : BaseChangeAvoid.Statement) : ChowHeightRecursion.Statement :=
  ChowHeightRecursion.proof hV hA hB hAv

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module Set

open scoped ENNReal

theorem AreaFormulaInjSet.proof (h : AreaFormulaLocal.Statement) : AreaFormulaInjSet.Statement := by
  classical
  intro E F _ _ _ _ _ _ _ _ _ _ k hk U A f hU hf hAU hA hinj
  set J : E → ℝ≥0∞ := fun x => ENNReal.ofReal (areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F)) with hJdef
  change μH[(k : ℝ)] (f '' A) = ∫⁻ x in A, J x ∂(μH[(k : ℝ)])
  have hdiff : ∀ x ∈ U, HasFDerivAt f (fderiv ℝ f x) x := fun x hx =>
    ((hf.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hx)).hasFDerivAt

  set C : Set E := A ∩ fderiv ℝ f ⁻¹' {L : E →L[ℝ] F | Function.Injective L}ᶜ with hCdef
  have hCm : MeasurableSet C :=
    hA.inter (measurable_fderiv ℝ f ContinuousLinearMap.isOpen_injective.measurableSet.compl)
  have hJC : EqOn J (fun _ => 0) C := by
    intro x hx
    have hni : ¬ Function.Injective (fderiv ℝ f x : E →ₗ[ℝ] F) := hx.2
    have h0 : (fderiv ℝ f x : E →ₗ[ℝ] F).normDet = 0 :=
      LinearMap.normDet_eq_zero_iff_ker_ne_bot.2 fun hk0 => hni (LinearMap.ker_eq_bot.1 hk0)
    simp [hJdef, SheetImageAreaSet.areaJacobian_eq_normDet, h0]
  have hCnull : μH[(k : ℝ)] (f '' C) = 0 := by
    let e : (Fin k → ℝ) ≃L[ℝ] E := (finBasisOfFinrankEq ℝ E hk).equivFun.symm.toContinuousLinearEquiv
    have himg : f '' C = (f ∘ e) '' (e ⁻¹' C) := by
      rw [image_comp, image_preimage_eq _ e.surjective]
    have key := IndefiniteRowSideFullHecke.ComplexSets.hausdorffMeasure_image_eq_zero_of_not_injective (f := f ∘ e)
      (s := e ⁻¹' C) (f' := fun x => (fderiv ℝ f (e x)).comp (e : (Fin k → ℝ) →L[ℝ] E)) ?_ ?_
    · rw [himg]
      simpa using key
    · intro x hx
      exact ((hdiff (e x) (hAU hx.1)).comp x e.hasFDerivAt).hasFDerivWithinAt
    · intro x hx hinj'
      apply hx.2
      intro a c hac
      have h2 := @hinj' (e.symm a) (e.symm c) (by simpa using hac)
      simpa using congrArg e h2

  set R : Set E := A \ C with hRdef
  have hRm : MeasurableSet R := hA.diff hCm
  set G : Set (Set E) := {V | IsOpen V ∧ V ⊆ U ∧ ∀ B ⊆ V, MeasurableSet B →
    μH[(k : ℝ)] (f '' B) = ∫⁻ x in B, J x ∂(μH[(k : ℝ)])} with hGdef
  have hRG : R ⊆ ⋃₀ G := by
    intro x hx
    have hxinj : Function.Injective (fderiv ℝ f x) := by
      by_contra hn
      exact hx.2 ⟨hx.1, hn⟩
    obtain ⟨V, hVo, hxV, hVU, hV⟩ := h E F k hk U f x hU hf (hAU hx.1) hxinj
    exact ⟨V, ⟨hVo, hVU, hV⟩, hxV⟩
  obtain ⟨T, hTc, hTG, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable G fun V hV => hV.1
  have hG0 : (∅ : Set E) ∈ G := ⟨isOpen_empty, empty_subset _, fun B hB _ => by
    rw [subset_empty_iff.1 hB]
    simp⟩
  obtain ⟨V, hVeq⟩ := (hTc.insert ∅).exists_eq_range (insert_nonempty _ _)
  have hVG : ∀ n, V n ∈ G := by
    intro n
    have hn : V n ∈ insert ∅ T := by
      rw [hVeq]
      exact mem_range_self n
    rcases hn with h0 | hT
    · rw [h0]
      exact hG0
    · exact hTG hT
  have hRV : R ⊆ ⋃ n, V n := by
    intro x hx
    have hx' : x ∈ ⋃₀ T := by
      rw [hTU]
      exact hRG hx
    obtain ⟨W, hWT, hxW⟩ := hx'
    have hW : W ∈ range V := by
      rw [← hVeq]
      exact mem_insert_of_mem _ hWT
    obtain ⟨n, rfl⟩ := hW
    exact mem_iUnion.2 ⟨n, hxW⟩

  set B : ℕ → Set E := fun n => R ∩ disjointed V n with hBdef
  have hBm : ∀ n, MeasurableSet (B n) := fun n =>
    hRm.inter (MeasurableSet.disjointed (fun m => (hVG m).1.measurableSet) n)
  have hBd : Pairwise (Function.onFun Disjoint B) := fun m n hmn =>
    ((disjoint_disjointed V) hmn).mono inter_subset_right inter_subset_right
  have hBU : ⋃ n, B n = R := by
    rw [← inter_iUnion, iUnion_disjointed]
    exact inter_eq_left.2 hRV
  have hBV : ∀ n, B n ⊆ V n := fun n => inter_subset_right.trans (disjointed_subset V n)
  have hBA : ∀ n, B n ⊆ A := fun n => inter_subset_left.trans sdiff_subset
  have hR : μH[(k : ℝ)] (f '' R) = ∫⁻ x in R, J x ∂(μH[(k : ℝ)]) := by
    rw [← hBU, image_iUnion, measure_iUnion, lintegral_iUnion hBm hBd]
    · exact tsum_congr fun n => (hVG n).2.2 (B n) (hBV n) (hBm n)
    · intro m n hmn
      refine disjoint_left.2 ?_
      rintro _ ⟨a, ha, rfl⟩ ⟨c, hc, hca⟩
      obtain rfl := hinj (hBA n hc) (hBA m ha) hca
      exact disjoint_left.1 (hBd hmn) ha hc
    · intro n
      exact (hBm n).image_of_continuousOn_injOn
        (hf.continuousOn.mono ((hBV n).trans (hVG n).2.1)) (hinj.mono (hBA n))

  have hAC : A = R ∪ C := (sdiff_union_of_subset inter_subset_left).symm
  have himgA : μH[(k : ℝ)] (f '' A) = μH[(k : ℝ)] (f '' R) := by
    apply le_antisymm
    · calc μH[(k : ℝ)] (f '' A) = μH[(k : ℝ)] (f '' R ∪ f '' C) := by
            rw [← image_union, ← hAC]
        _ ≤ μH[(k : ℝ)] (f '' R) + μH[(k : ℝ)] (f '' C) := measure_union_le _ _
        _ = μH[(k : ℝ)] (f '' R) := by rw [hCnull, add_zero]
    · exact measure_mono (image_mono sdiff_subset)
  have hintA : ∫⁻ x in A, J x ∂(μH[(k : ℝ)]) = ∫⁻ x in R, J x ∂(μH[(k : ℝ)]) := by
    calc ∫⁻ x in A, J x ∂(μH[(k : ℝ)]) = ∫⁻ x in R ∪ C, J x ∂(μH[(k : ℝ)]) := by rw [← hAC]
      _ = ∫⁻ x in R, J x ∂(μH[(k : ℝ)]) + ∫⁻ x in C, J x ∂(μH[(k : ℝ)]) :=
          lintegral_union hCm disjoint_sdiff_left
      _ = ∫⁻ x in R, J x ∂(μH[(k : ℝ)]) := by
          rw [setLIntegral_congr_fun hCm hJC, lintegral_zero, add_zero]
  rw [himgA, hR, hintA]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

noncomputable section

def TangentJacCompress.Statement : Prop :=
  ∀ (n m : ℕ) (π : Fin m → Fin n → ℂ) (T : Submodule ℂ (EuclideanSpace ℂ (Fin n))),
    ((tangentJac π T : ℝ) : ℂ) =
      (T.starProjection ∘L (LinearMap.toContinuousLinearMap (linProjₗ π)).adjoint ∘L
          LinearMap.toContinuousLinearMap (linProjₗ π) ∘L T.starProjection +
        (1 - T.starProjection)).det

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

def LeadPlaneJac.Statement : Prop :=
  ∀ (m k : ℕ) (π : Fin m → Fin (m + k) → ℂ),
    tangentJac π (leadCoordPlane (m + k) m) = ‖(coordPlaneBlock π).det‖ ^ 2

end

end GroundTheory.Heights₂.Heights
end
