module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PAffineChartTrdeg
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle058
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle016
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChowFormExists
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Algebra.MvPolynomial.Nilpotent
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
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial

theorem ClosedPointChartField.proof : ClosedPointChartField.Statement := by
  intro F _ n I i hI hdim hXi
  have := hI.isPrime
  set ξ := genPt I
  have hξ : ξ i ≠ 0 := fun h =>
    hXi ((ChartZeroTrdeg.aeval_genPt_eq_zero_iff' I (X i)).1 (by simpa using h))
  set g : MvPolynomial (Fin n) F →ₐ[F] FractionRing (MvPolynomial (Fin n) F ⧸ I) :=
    aeval fun m => ξ m * (ξ i)⁻¹ with hg

  have hhom : ∀ (h : MvPolynomial (Fin n) F) (d : ℕ), h.IsHomogeneous d →
      ChartZeroTrdeg.homogAt h i d = h := by
    intro h d hh
    conv_rhs => rw [h.as_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    have hα' : (α.sum fun _ e => e) = d := by
      have := hh (mem_support_iff.mp hα)
      simpa [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] using this
    rw [hα', Nat.sub_self, pow_zero, mul_one]

  have hker : RingHom.ker g = I ⊔ Ideal.span {X i - 1} := by
    apply le_antisymm
    · intro p hp
      rw [RingHom.mem_ker] at hp
      have hH : ChartZeroTrdeg.homogAt p i p.totalDegree ∈ I := by
        rw [← ChartZeroTrdeg.aeval_genPt_eq_zero_iff',
          ChartZeroTrdeg.aeval_homogAt p i _ le_rfl ξ hξ]
        rw [← hg, hp, mul_zero]
      have hd : p - ChartZeroTrdeg.homogAt p i p.totalDegree ∈ Ideal.span {X i - 1} := by
        rw [← Ideal.Quotient.eq]
        have h1 : Ideal.Quotient.mk (Ideal.span {X i - 1}) (X i : MvPolynomial (Fin n) F) = 1 := by
          rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
          exact Ideal.subset_span rfl
        conv_lhs => rw [p.as_sum]

        simp only [ChartZeroTrdeg.homogAt, map_sum, map_mul, map_pow, h1, one_pow, mul_one]
      have := (I ⊔ Ideal.span {X i - 1}).add_mem (Ideal.mem_sup_left hH) (Ideal.mem_sup_right hd)
      simpa using this
    · refine sup_le ?_ ?_
      · intro f hf

        rw [RingHom.mem_ker, ← sum_homogeneousComponent f, map_sum]
        refine Finset.sum_eq_zero fun d _ => ?_
        have hh : (homogeneousComponent d f).IsHomogeneous d :=
          homogeneousComponent_isHomogeneous d f
        have h0 : aeval ξ (homogeneousComponent d f) = 0 :=
          (ChartZeroTrdeg.aeval_genPt_eq_zero_iff' I _).2 (hI.isHomog f hf d)
        by_cases hz : homogeneousComponent d f = 0
        · rw [hz, map_zero]
        have := ChartZeroTrdeg.aeval_homogAt (homogeneousComponent d f) i d
          (hh.totalDegree hz).le ξ hξ
        rw [hhom _ d hh, h0] at this
        exact (mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero _ hξ)
      · rw [Ideal.span_le, Set.singleton_subset_iff]
        change g (X i - 1) = 0
        simp [hg, hξ]

  let e : (MvPolynomial (Fin n) F ⧸ (I ⊔ Ideal.span {X i - 1})) ≃ₐ[F] g.range :=
    (Ideal.quotientEquivAlgOfEq F (hker.symm.trans (AlgHom.ker_rangeRestrict g).symm)).trans
      (Ideal.quotientKerAlgEquivOfSurjective g.rangeRestrict_surjective)
  have htr := GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof F n 0 I i hI (by simpa using hdim) hXi
  rw [Algebra.adjoin_range_eq_range_aeval] at htr
  have halg : Algebra.IsAlgebraic F g.range := trdeg_eq_zero_iff.1 (by simpa using htr)
  have hfield : IsField g.range := isField_of_isIntegral_of_isField' (Field.toIsField F)
  have : Algebra.FiniteType F g.range :=
    Algebra.FiniteType.of_surjective g.rangeRestrict g.rangeRestrict_surjective
  have : Module.Finite F g.range := Algebra.IsIntegral.finite
  exact ⟨MulEquiv.isField hfield e.toMulEquiv, Module.Finite.equiv e.symm.toLinearEquiv⟩

end ObjectsChow

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal

theorem AreaFormulaInj.proof (h : AreaFormulaInjSet.Statement) : AreaFormulaInj.Statement := by
  classical
  intro E F _ _ _ _ _ _ _ _ _ _ k hk U A f g hU hf hAU hA hinj hg
  let f' : E → F := U.piecewise f (fun _ => 0)
  have hf'm : Measurable f' := hf.continuousOn.measurable_piecewise continuousOn_const hU.measurableSet
  have hEq : ∀ x ∈ A, f' x = f x := fun x hx => Set.piecewise_eq_of_mem _ _ _ (hAU hx)
  have hJ : Measurable fun x : E => ENNReal.ofReal (areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F)) :=
    ENNReal.measurable_ofReal.comp (continuous_areaJacobian.measurable.comp (measurable_fderiv ℝ f))
  let ρ : Measure E := ((μH[(k : ℝ)] : Measure E).restrict A).withDensity
    fun x : E => ENNReal.ofReal (areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F))
  have hmap : ρ.map f' = (μH[(k : ℝ)] : Measure F).restrict (f '' A) := by
    ext S hS
    have hpre : MeasurableSet (f' ⁻¹' S) := hf'm hS
    rw [Measure.map_apply hf'm hS, withDensity_apply _ hpre, Measure.restrict_restrict hpre,
      Measure.restrict_apply hS,
      ← h E F k hk U _ f hU hf (by exact fun x hx => hAU hx.2) (hpre.inter hA) (hinj.mono fun x hx => hx.2)]
    congr 1
    ext z
    constructor
    · rintro ⟨y, ⟨hyS, hyA⟩, rfl⟩
      exact ⟨by simpa [Set.mem_preimage, hEq y hyA] using hyS, y, hyA, rfl⟩
    · rintro ⟨hzS, y, hyA, rfl⟩
      exact ⟨y, ⟨by simpa [Set.mem_preimage, hEq y hyA] using hzS, hyA⟩, rfl⟩
  calc ∫⁻ y in f '' A, g y ∂(μH[(k : ℝ)]) = ∫⁻ z, g z ∂(ρ.map f') := by rw [hmap]
    _ = ∫⁻ x, g (f' x) ∂ρ := lintegral_map hg hf'm
    _ = ∫⁻ x in A, ENNReal.ofReal (areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F)) * g (f' x)
          ∂(μH[(k : ℝ)]) := lintegral_withDensity_eq_lintegral_mul _ hJ (hg.comp hf'm)
    _ = _ := setLIntegral_congr_fun hA fun x hx => by rw [hEq x hx, mul_comm]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem SectionOrderAlgClosed.proof (h₁ : IncIdealBelow.Statement) (h₂ : SpecFirstMemIncIdeal.Statement)
    (h₃ : ChartChoiceAlgClosed.Statement) (h₄ : Vertical.SpecFirstNeField.Statement)
    (h₅ : LocalizationPrimeDVR.Statement) (h₆ : EmultiplicityOrd.Statement) (h₇ : ChartFinite.Statement)
    (h₈ : ChartLocDomain.Statement) (h₉ : ChartNormAlgClosed.Statement)
    (h₁₀ : ChartLengthAlgClosed.Statement) (h₁₁ : LengthQuotientDet.Statement) :
    SectionOrderAlgClosed.Statement := by
  intro F _ _ n e I f u hI hf hu
  have hne : specFirst f u ≠ 0 := h₄ F n e I f u hI hf hu
  refine ⟨hne, fun q hq => ?_⟩
  have hqp : Prime q := hq.prime
  obtain ⟨t, ht⟩ := h₃ F n e I f q hI hf hqp

  have htI : linForm t ∉ I := by
    intro h
    have hmem := h₂ F n e I I f t hf le_rfl h
    rw [h₁ F n e I f hI hf, Ideal.mem_bot] at hmem
    exact ht (hmem ▸ dvd_zero q)
  let p : Ideal (MvPolynomial (Fin e × Fin n) F) := Ideal.span {q}
  have hpp : p.IsPrime := (Ideal.span_singleton_prime hqp.ne_zero).mpr hqp
  have htp : specFirst f t ∉ p := by
    rw [Ideal.mem_span_singleton]
    exact ht
  have : IsDiscreteValuationRing (Localization.AtPrime p) := h₅ _ q p hqp rfl
  have hem := h₆ _ q (specFirst f u) p hqp rfl hne
  have : Module.Finite (Localization.AtPrime p) (ChartLoc I t e p) := h₇ F n e I f t p hI hf htp
  obtain ⟨_, hinj, -⟩ := h₈ F n e I f t p hI hf htI
  have : Module.IsTorsionFree (Localization.AtPrime p) (ChartLoc I t e p) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact hinj
  have : Module.Free (Localization.AtPrime p) (ChartLoc I t e p) :=
    Module.free_of_finite_type_torsion_free'
  have hnorm := h₉ F n e I f t p hI hf (Or.inr ⟨q, hqp, rfl⟩) htp u
  have hunit : IsUnit (algebraMap _ (Localization.AtPrime p) (specFirst f t)) :=
    IsLocalization.map_units (Localization.AtPrime p) (⟨specFirst f t, htp⟩ : p.primeCompl)
  have hinjO : Function.Injective
      (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) :=
    IsLocalization.injective _ p.primeCompl_le_nonZeroDivisors
  have hdet : LinearMap.det (LinearMap.mulLeft (Localization.AtPrime p)
      (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u))) ≠ 0 := by
    intro h0
    apply hne
    apply hinjO
    rw [hnorm, h0, mul_zero, map_zero]
  have hlen := h₁₁ (Localization.AtPrime p) (ChartLoc I t e p) _ hdet
  rw [hem, hnorm, Ring.ord_mul_of_isUnit_left hunit, ← hlen]
  exact h₁₀ F n e I f t u q p hI hf hu hqp rfl ht

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

open scoped ENNReal

noncomputable section

variable {m n : ℕ}

theorem HermNorm.pointOf_add' (h : HermNorm n) (v w : EuclideanSpace ℂ (Fin n)) :
    h.pointOf (v + w) = h.pointOf v + h.pointOf w := by
  simp only [HermNorm.pointOf]
  rw [← Matrix.mulVec_add]
  rfl

theorem HermNorm.pointOf_smul' (h : HermNorm n) (c : ℂ) (v : EuclideanSpace ℂ (Fin n)) :
    h.pointOf (c • v) = c • h.pointOf v := by
  simp only [HermNorm.pointOf]
  rw [← Matrix.mulVec_smul]
  rfl

def coneTangent (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (y : EuclideanSpace ℂ (Fin n)) : Submodule ℂ (EuclideanSpace ℂ (Fin n)) where
  carrier := {v | ∀ q ∈ J, ∑ j, eval (h.pointOf y) (pderiv j q) * h.pointOf v j = 0}
  add_mem' {v w} hv hw q hq := by
    simp only [HermNorm.pointOf_add', Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [hv q hq, hw q hq, add_zero]
  zero_mem' q _ := by
    have h0 : h.pointOf 0 = 0 := by simpa using h.pointOf_smul' 0 0
    simp [h0]
  smul_mem' c v hv q hq := by
    simp only [HermNorm.pointOf_smul', Pi.smul_apply, smul_eq_mul, mul_left_comm _ c,
      ← Finset.mul_sum]
    rw [hv q hq, mul_zero]

def tangentJac (π : Fin m → Fin n → ℂ) (T : Submodule ℂ (EuclideanSpace ℂ (Fin n))) : ℝ :=
  LinearMap.normDet (𝕜 := ℂ) (U := T) (V := EuclideanSpace ℂ (Fin m)) ((linProjₗ π).comp T.subtype) ^ 2

def coneJac (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (π : Fin m → Fin n → ℂ)
    (y : EuclideanSpace ℂ (Fin n)) : ℝ :=
  tangentJac π (coneTangent h J y)

def firstCoordVec (n : ℕ) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 fun j => if (j : ℕ) = 0 then 1 else 0

def leadCoordPlane (n m : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Fin n)) where
  carrier := {y | ∀ j : Fin n, m ≤ (j : ℕ) → y j = 0}
  add_mem' {v w} hv hw j hj := by
    simp [hv j hj, hw j hj]
  zero_mem' j _ := by
    simp
  smul_mem' c v hv j hj := by
    simp [hv j hj]

def tangentGaussProfile (n m : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
    (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π ((r : ℂ) • firstCoordVec n)) *
      ENNReal.ofReal (tangentJac π (leadCoordPlane n m))

def ConeAreaFormula.Statement : Prop :=
  ∀ (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → 0 < m → m ≤ n →
    (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
    ∀ (π : Fin m → Fin n → ℂ) (g : EuclideanSpace ℂ (Fin m) → ℝ≥0∞), Measurable g →
      volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ y in coneSet h J, g (linProj π y) * ENNReal.ofReal (coneJac h J π y)
            ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) =
        Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ w : EuclideanSpace ℂ (Fin m), (fibreCount h J π w : ℝ≥0∞) * g w

def ConeTangentAverage.Statement : Prop :=
  ∀ (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → 0 < m → m ≤ n →
    (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
      ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
          ∫⁻ y in coneSet h J,
            (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
              ENNReal.ofReal (coneJac h J π y) ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) =
        ∫⁻ y in coneSet h J, tangentGaussProfile n m ‖y‖ ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ))

def ConeRadialIntegral.Statement : Prop :=
  ∀ (n m : ℕ), 0 < m → ∀ C : Set (EuclideanSpace ℂ (Fin n)),
    (∀ y ∈ C, ∀ t : ℝ, 0 < t → t • y ∈ C) →
    Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) {y | ‖y‖ < 1 ∧ y ∈ C} < ⊤ →
    ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ y in C, f ‖y‖ ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) =
        Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) {y | ‖y‖ < 1 ∧ y ∈ C} *
          ∫⁻ r in Set.Ioi (0 : ℝ), f r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1))

def TangentGaussMoment.Statement : Prop :=
  ∀ (n m : ℕ), 0 < m → m ≤ n →
    Measurable (tangentGaussProfile n m) ∧ AntitoneOn (tangentGaussProfile n m) (Set.Ici 0) ∧
      (∀ r : ℝ, 0 < tangentGaussProfile n m r) ∧
      0 < ∫⁻ r in Set.Ioi (0 : ℝ), tangentGaussProfile n m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1)) ∧
      ∫⁻ r in Set.Ioi (0 : ℝ), tangentGaussProfile n m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1)) < ⊤

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem IncIdealNeBotDim.proof (h₁ : IncIdealDim.Statement) : IncIdealNeBotDim.Statement := by
  intro F _ n k Q hQ hI
  have := hQ.isPrime
  obtain ⟨j, -⟩ := hQ.isRelevant
  have hn : 0 < n := j.pos

  have hle : ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) ≤ ((n : ℕ) : WithBot ℕ∞) := by
    have h := ringKrullDim_le_of_surjective (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective
    rwa [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) = ((m : ℕ) : WithBot ℕ∞) := by
    have hbot : ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) ≠ ⊥ :=
      ne_bot_of_le_ne_bot (by simp) ringKrullDim_nonneg_of_nontrivial
    generalize ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) = D at hle hbot ⊢
    induction D using WithBot.recBotCoe with
    | bot => exact absurd rfl hbot
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        exfalso
        have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast hle
        exact ENat.natCast_ne_top n (top_le_iff.mp (WithBot.coe_le_coe.mp h'))
      | coe m => exact ⟨m, rfl⟩
  have hm1 : 1 ≤ m := one_le_of_isProjPrime hQ hm
  rw [hm]
  by_contra hlt
  have hkm : k < m := by
    by_contra h
    exact hlt (by exact_mod_cast Nat.le_of_not_lt h)

  have hdim := h₁ F n k (m - 1) Q hQ (by rw [Nat.sub_add_cancel hm1]; exact hm)
  have hmin : min k (m - 1) = k := min_eq_left (by omega)
  have hkn : k ≤ k * n := Nat.le_mul_of_pos_right k hn
  rw [hmin, Nat.sub_add_cancel hkn] at hdim

  obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hgnz : g ∈ nonZeroDivisors (MvPolynomial (Fin k × Fin n) F) := mem_nonZeroDivisors_of_ne_zero hg0
  have h2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hgnz
  have h3 : ringKrullDim (MvPolynomial (Fin k × Fin n) F ⧸ incIdeal Q k) ≤
      ringKrullDim (MvPolynomial (Fin k × Fin n) F ⧸ Ideal.span {g}) :=
    ringKrullDim_le_of_surjective
      (Ideal.Quotient.factor ((Ideal.span_singleton_le_iff_mem _).mpr hg))
      (Ideal.Quotient.factor_surjective _)
  have hS : ringKrullDim (MvPolynomial (Fin k × Fin n) F) = ((k * n : ℕ) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, zero_add]
  rw [hdim] at h3
  rw [hS] at h2
  have h4 : (((k * n : ℕ) : WithBot ℕ∞)) + 1 ≤ ((k * n : ℕ) : WithBot ℕ∞) :=
    le_trans (add_le_add h3 le_rfl) h2
  have h5 : ((k * n + 1 : ℕ) : WithBot ℕ∞) ≤ ((k * n : ℕ) : WithBot ℕ∞) := by exact_mod_cast h4
  have h6 : k * n + 1 ≤ k * n := by exact_mod_cast h5
  omega

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem ChowFormAssoc.proof : ChowFormAssoc.Statement := by
  intro F _ n k I g g' hg hg'
  have h1 : g ∣ g' := (hg.2 g').mp ((hg'.2 g').mpr dvd_rfl)
  have h2 : g' ∣ g := (hg'.2 g).mp ((hg.2 g).mpr dvd_rfl)
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd h1 h2
  obtain ⟨c, hc, hcu⟩ :=
    (isUnit_iff_eq_C_of_isReduced (P := (u : MvPolynomial (Fin k × Fin n) F))).mp u.isUnit
  refine ⟨c, hc.ne_zero, ?_⟩
  rw [← hu, hcu, mul_comm]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem ChowFormCycleSmul.proof : ChowFormCycleSmul.Statement := by
  intro F _ n k m Z f hZ
  obtain ⟨c, hc, g, hg, hf⟩ := hZ
  refine ⟨c ^ m, pow_ne_zero _ hc, g, fun W hW => hg W (Finsupp.support_smul hW), ?_⟩
  have hsub : (m • Z).support ⊆ Z.support := Finsupp.support_smul
  rw [Finset.prod_subset hsub (fun W _ hW => by rw [Finsupp.notMem_support_iff.mp hW, pow_zero]), hf,
    mul_pow, ← map_pow, ← Finset.prod_pow]
  congr 1
  refine Finset.prod_congr rfl fun W _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, ← pow_mul, mul_comm]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem EvalSpecFirst.proof : EvalSpecFirst.Statement := by
  intro n k f v w
  change eval₂Hom (RingHom.id ℂ) w (bind₁ (specFirstVar v) f) =
    eval₂Hom (RingHom.id ℂ) (consGroup v w) f
  rw [eval₂Hom_bind₁]
  congr 2
  funext ij
  obtain ⟨i, j⟩ := ij
  induction i using Fin.cases with
  | zero => simp [specFirstVar, consGroup]
  | succ i => simp [specFirstVar, consGroup]

end GroundTheory.Heights₂.Heights
end
