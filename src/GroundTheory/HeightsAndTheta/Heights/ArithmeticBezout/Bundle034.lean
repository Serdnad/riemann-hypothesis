module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsGraphAreaFibre
public import Mathlib.Order.CompletePartialOrder
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal

noncomputable section

theorem volume_null_of_hausdorff_null {m : ℕ} {s : Set (EuclideanSpace ℂ (Fin m))}
    (hs : Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) s = 0) : volume s = 0 := by
  have hdim : finrank ℝ (EuclideanSpace ℂ (Fin m)) = 2 * m := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  have hμ : (Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) : Measure (EuclideanSpace ℂ (Fin m))) =
      Measure.hausdorffMeasure (finrank ℝ (EuclideanSpace ℂ (Fin m)) : ℝ) := by
    rw [hdim]
  rw [hμ] at hs
  exact Measure.absolutelyContinuous_isAddHaarMeasure volume
    (Measure.hausdorffMeasure (finrank ℝ (EuclideanSpace ℂ (Fin m)) : ℝ)) hs

theorem encard_iUnion_disjoint_nat {α : Type*} (s : ℕ → Set α) (hs : Pairwise (Function.onFun Disjoint s)) :
    (((⋃ i, s i).encard : ℕ∞) : ℝ≥0∞) = ∑' i, (((s i).encard : ℕ∞) : ℝ≥0∞) := by
  let _ : MeasurableSpace α := ⊤
  have hm : ∀ t : Set α, MeasurableSet t := fun _ => MeasurableSpace.measurableSet_top
  rw [← Measure.count_apply (hm _), measure_iUnion hs (fun _ => hm _)]
  simp only [Measure.count_apply (hm _)]

theorem volume_linProj_image_null {m n : ℕ} (π : Fin m → Fin n → ℂ) {s : Set (EuclideanSpace ℂ (Fin n))}
    (hs : Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) s = 0) : volume (linProj π '' s) = 0 := by
  refine volume_null_of_hausdorff_null (nonpos_iff_eq_zero.1 ?_)
  have hL := (LinearMap.toContinuousLinearMap (linProjₗ π)).lipschitz.hausdorffMeasure_image_le
    (d := ((2 * m : ℕ) : ℝ)) (by positivity) s
  rw [LinearMap.coe_toContinuousLinearMap', hs, mul_zero] at hL
  exact hL

theorem ConeAreaFormula.proof (hCover : ConeGraphCover.Statement) (hArea : GraphAreaFibre.Statement) :
    ConeAreaFormula.Statement := by
  intro n m h J hJ hm hmn hfin π g hg
  obtain ⟨e, Ω, Φ, hpc, hnull⟩ := hCover n m h J hJ hm hmn hfin
  let S : ℕ → Set (EuclideanSpace ℂ (Fin n)) := fun i => graphPt (e i) (Φ i) '' Ω i
  let D := disjointed S
  have hSm : ∀ i, MeasurableSet (S i) := fun i =>
    (hpc i).1.measurableSet.image_of_continuousOn_injOn
      (continuousOn_graphPt _ (hpc i).2.1.continuousOn) (graphPt_injective_of_graphBase _ _).injOn
  have hDm : ∀ i, MeasurableSet (D i) := MeasurableSet.disjointed hSm
  have hDS : ∀ i, D i ⊆ S i := disjointed_subset S
  have hDd : Pairwise (Function.onFun Disjoint D) := disjoint_disjointed S
  have hU : ⋃ i, D i = ⋃ i, S i := iUnion_disjointed
  have hUC : ⋃ i, D i ⊆ coneSet h J := Set.iUnion_subset fun i => (hDS i).trans (hpc i).2.2.1
  have hN : Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (coneSet h J \ ⋃ i, D i) = 0 := by
    rw [hU]; exact hnull
  have hCae : coneSet h J =ᵐ[Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)] ⋃ i, D i :=
    ae_eq_set.2 ⟨hN, by rw [Set.sdiff_eq_empty.2 hUC]; exact measure_empty⟩
  have hpiece := fun i => hArea m (n - m) n (e i) (Ω i) (Φ i) (hpc i).1 (hpc i).2.1 (D i) (hDS i)
    (hDm i) (coneTangent h J) (fun x hx _ => (hpc i).2.2.2 x hx) π
  have hcount : ∀ᵐ w ∂(volume : Measure (EuclideanSpace ℂ (Fin m))),
      ((fibreCount h J π w : ℕ∞) : ℝ≥0∞) * g w =
        ∑' i, (({y | y ∈ D i ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞) * g w := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (volume_linProj_image_null π hN)] with w hw
    rw [ENNReal.tsum_mul_right, fibreCount, ← encard_iUnion_disjoint_nat]
    · congr 3
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨hy, rfl⟩
        by_contra hne
        exact hw ⟨y, ⟨hy, fun hyD => hne (by
          obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hyD
          exact ⟨i, hi, rfl⟩)⟩, rfl⟩
      · rintro ⟨i, hi, hw'⟩
        exact ⟨hUC (Set.mem_iUnion.2 ⟨i, hi⟩), hw'⟩
    · intro i j hij
      exact (hDd hij).mono (fun y hy => hy.1) (fun y hy => hy.1)
  calc volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
        ∫⁻ y in coneSet h J, g (linProj π y) * ENNReal.ofReal (coneJac h J π y)
          ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ))
      = ∑' i, volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ y in D i, g (linProj π y) * ENNReal.ofReal (coneJac h J π y)
            ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) := by
        rw [Measure.restrict_congr_set hCae, lintegral_iUnion hDm hDd, ENNReal.tsum_mul_left]
    _ = ∑' i, Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ w, (({y | y ∈ D i ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞) * g w :=
        tsum_congr fun i => (hpiece i).2 g hg
    _ = Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ w, ((fibreCount h J π w : ℕ∞) : ℝ≥0∞) * g w := by
        rw [ENNReal.tsum_mul_left, ← lintegral_tsum
          (f := fun i w => (({y | y ∈ D i ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞) * g w)
          fun i => (hpiece i).1.mul hg.aemeasurable, lintegral_congr_ae hcount]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module Set

open scoped ENNReal

noncomputable section

theorem GraphAreaFibre.differentiableAt_graphPt {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    {Φ : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)} {x : EuclideanSpace ℂ (Fin d)}
    (hΦ : DifferentiableAt ℂ Φ x) : DifferentiableAt ℂ (graphPt e Φ) x := by
  rw [differentiableAt_piLp]
  intro j
  show DifferentiableAt ℂ (fun y => Sum.elim (fun i => y i) (fun i => Φ y i) (e j)) x
  rcases e j with i | i
  · exact (differentiableAt_piLp 2).1 differentiableAt_id i
  · exact (differentiableAt_piLp 2).1 hΦ i

theorem GraphAreaFibre.continuous_graphBase {d k n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin k) :
    Continuous (graphBase e : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin d)) := by
  unfold graphBase
  fun_prop

theorem GraphAreaFibre.proof (hInt : GraphAreaIntegral.Statement) (hJac : TangentJacComp.Statement)
    (hMult : AreaMultiplicityWeight.Statement) : GraphAreaFibre.Statement := by
  intro d k n e Ω Φ hΩ hΦ P hPΩ hPm T hT π
  set G : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin n) := graphPt e Φ with hGdef
  set μ : Measure (EuclideanSpace ℂ (Fin d)) := Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) with hμdef
  have hdim : ((2 * d : ℕ) : ℝ) = (finrank ℝ (EuclideanSpace ℂ (Fin d)) : ℝ) := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  have : μ.IsAddHaarMeasure := by
    rw [hμdef, hdim]
    infer_instance

  set A : Set (EuclideanSpace ℂ (Fin d)) := Ω ∩ G ⁻¹' P with hAdef
  have hAΩ : A ⊆ Ω := inter_subset_left
  have hGA : G '' A = P := by
    rw [hAdef, image_inter_preimage]
    exact inter_eq_right.2 hPΩ
  have hAm : MeasurableSet A := by
    have hAeq : A = graphBase e '' P := by
      ext x
      constructor
      · rintro ⟨-, hxP⟩
        exact ⟨G x, hxP, graphBase_graphPt e Φ x⟩
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨x, hx, rfl⟩ := hPΩ hy
        rw [graphBase_graphPt]
        exact ⟨hx, hy⟩
    rw [hAeq]
    refine hPm.image_of_continuousOn_injOn (GraphAreaFibre.continuous_graphBase e).continuousOn ?_
    intro y hy y' hy' h
    obtain ⟨x, -, rfl⟩ := hPΩ hy
    obtain ⟨x', -, rfl⟩ := hPΩ hy'
    rw [hGdef, graphBase_graphPt, graphBase_graphPt] at h
    rw [h]

  have hGd : ∀ x ∈ Ω, DifferentiableAt ℂ G x := fun x hx =>
    GraphAreaFibre.differentiableAt_graphPt e ((hΦ x hx).differentiableAt (hΩ.mem_nhds hx))
  let Lπ : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin d) :=
    LinearMap.toContinuousLinearMap (linProjₗ π)
  set f : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin d) := fun x => linProj π (G x) with hfdef
  have hfd : ∀ x ∈ Ω, HasFDerivAt f ((Lπ.comp (fderiv ℂ G x)).restrictScalars ℝ) x := fun x hx =>
    (Lπ.hasFDerivAt.comp x (hGd x hx).hasFDerivAt).restrictScalars ℝ
  have hf' : ∀ x ∈ A, HasFDerivWithinAt f (fderiv ℝ f x) A x := fun x hx =>
    (hfd x (hAΩ hx)).differentiableAt.hasFDerivAt.hasFDerivWithinAt
  obtain ⟨hNm, hN⟩ := hMult (EuclideanSpace ℂ (Fin d)) μ A f (fun x => fderiv ℝ f x) hAm hf'

  have hcount : ∀ w, {y | y ∈ P ∧ linProj π y = w}.encard = {x ∈ A | f x = w}.encard := by
    intro w
    have hset : {y | y ∈ P ∧ linProj π y = w} = G '' {x ∈ A | f x = w} := by
      ext y
      constructor
      · rintro ⟨hy, hyw⟩
        obtain ⟨x, hx, rfl⟩ := hPΩ hy
        exact ⟨x, ⟨⟨hx, hy⟩, hyw⟩, rfl⟩
      · rintro ⟨x, ⟨⟨-, hxP⟩, hxw⟩, rfl⟩
        exact ⟨hxP, hxw⟩
    rw [hset, (graphPt_injective_of_graphBase e Φ).injOn.encard_image]
  have hNfun : (fun w : EuclideanSpace ℂ (Fin d) =>
      (({y | y ∈ P ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞)) =
      fun w => (({x ∈ A | f x = w}.encard : ℕ∞) : ℝ≥0∞) := by
    funext w
    rw [hcount w]

  have hc : μ = μ.addHaarScalarFactor volume • volume := Measure.isAddLeftInvariant_eq_smul μ volume
  refine ⟨?_, fun g hg => ?_⟩
  · rw [hNfun]
    exact hNm.mono_ac (Measure.absolutelyContinuous_isAddHaarMeasure volume μ)

  have h1 : ∫⁻ y in P, g (linProj π y) * ENNReal.ofReal (tangentJac π (T y))
      ∂(Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ)) =
      ∫⁻ x in A, g (f x) * ENNReal.ofReal |(fderiv ℝ f x).det| ∂μ := by
    rw [← hGA, hInt d k n e Ω Φ hΩ hΦ A hAΩ hAm]
    refine setLIntegral_congr_fun hAm fun x hx => ?_
    have hG' : fderiv ℝ G x = (fderiv ℂ G x).restrictScalars ℝ :=
      ((hGd x (hAΩ hx)).hasFDerivAt.restrictScalars ℝ).fderiv
    have hf'x : fderiv ℝ f x = (Lπ.comp (fderiv ℂ G x)).restrictScalars ℝ := (hfd x (hAΩ hx)).fderiv
    have hJ := hJac d n (fderiv ℂ G x : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) π
    have hTx : T (G x) = LinearMap.range (fderiv ℂ G x :
        EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := hT x (hAΩ hx) hx.2
    have hnn : 0 ≤ tangentJac π (T (G x)) := by
      unfold tangentJac
      positivity
    rw [mul_assoc, ← ENNReal.ofReal_mul hnn, hTx, hG', hf'x]
    congr 2
  rw [h1, hN g hg]
  simp_rw [hcount]
  rw [hc, Measure.smul_apply, lintegral_smul_measure]
  simp only [ENNReal.smul_def, smul_eq_mul]
  ring

end

end GroundTheory.Heights₂.Heights
end
