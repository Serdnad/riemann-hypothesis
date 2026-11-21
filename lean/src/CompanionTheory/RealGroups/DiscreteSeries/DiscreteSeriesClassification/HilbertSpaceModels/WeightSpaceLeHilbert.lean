import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.WeightSpaceLeHilbert
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.HilbertSpaceModels.StepSqInt

namespace CompanionTheory.RgDs.Hilb

open Finset Matrix
open ReciprocityTheory.ChartRestriction.DS

theorem weight_space_le_hilbert {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) : V1 ε Ψ ≤ Hlam ε Ψ T.w :=
  PositivityTheory.RgDs.Hilb.weight_space_le_hilbert Ψ

theorem hilb_of (h1 : StepStable) (h2 : StepDatum) (h0 : StepSig) (h3 : StepMoll) (h4 : StepWtSpan)
    (h5 : StepStable → StepMoll → StepWtSpan → StepCone)
    (h6 : StepStable → StepMoll → StepWtSpan → StepDatum → StepLowEq)
    (h7 : StepDatum → StepIrred) (h8 : StepDatum → StepFormulaF) (h10 : StepSig → StepSqInt)
    (h9 : StepVogan) : Hilb :=
  PositivityTheory.RgDs.Hilb.hilb_of h1 h2 h0 h3 h4 h5 h6 h7 h8 h10 h9

end CompanionTheory.RgDs.Hilb
