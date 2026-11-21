import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.HilbertLowestWeightOfInputs
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.HilbertSpaceModels.StepSqInt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.VNormSqLowKSubRootLt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeHW
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeExpK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfCharDataA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ComplexNormedInstanceCompat

namespace CompanionTheory.RgDs.Hilb

open Finset
open ReciprocityTheory.ChartRestriction.DS

alias hloweq_transfer := PositivityTheory.RgDs.Hilb.hloweq_transfer
alias hloweq_brIdx := PositivityTheory.RgDs.Hilb.hloweq_brIdx

theorem hloweq_eq_of_cone {n : ℕ} {ε : Fin n → Bool} {ν Λ : Fin n → ℝ} (h1 : InCone Λ ν)
    (h2 : Formalism.MainNotions.S.CDom ε ν Λ) : ν = Λ :=
  PositivityTheory.RgDs.Hilb.hloweq_eq_of_cone h1 h2

theorem hilbert_lowest_weight_of_inputs : StepStable → StepMoll → StepWtSpan → StepDatum → StepLowEq :=
  PositivityTheory.RgDs.Hilb.hilbert_lowest_weight_of_inputs

end CompanionTheory.RgDs.Hilb
