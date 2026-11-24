module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsAreaMultiplicityWeight
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAreaMultiplicity
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module Set Filter Function

open scoped ENNReal NNReal

noncomputable section

theorem AreaMultiplicityWeight.setLIntegral_comp_mul_abs_det₀ {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set E} {f : E → E} {f' : E → E →L[ℝ] E}
    (hs : NullMeasurableSet s μ) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hf : InjOn f s) (g : E → ℝ≥0∞) :
    ∫⁻ x in s, g (f x) * ENNReal.ofReal |(f' x).det| ∂μ = ∫⁻ y in f '' s, g y ∂μ :=
  AreaMultiplicityWeight.setLIntegral_comp_mul_abs_det_of_injective μ hs hf' hf g

theorem AreaMultiplicityWeight.proof : AreaMultiplicityWeight.Statement :=
  AreaMultiplicityWeight.lintegral_eq_lintegral_encard_mul

end

end GroundTheory.Heights₂.Heights
