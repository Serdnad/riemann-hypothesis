import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.HilbertSquareIntegrableOfSignature
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.HilbertSpaceModels.StepSqInt

namespace CompanionTheory.RgDs.Hilb

alias hq_umem := PositivityTheory.RgDs.Hilb.hq_umem
alias hq_one := PositivityTheory.RgDs.Hilb.hq_one
alias hq_mul := PositivityTheory.RgDs.Hilb.hq_mul
alias hq_iso := PositivityTheory.RgDs.Hilb.hq_iso
alias hq_memLp_of_ne := PositivityTheory.RgDs.Hilb.hq_memLp_of_ne
alias hq_inner := PositivityTheory.RgDs.Hilb.hq_inner
alias hq_w_ne := PositivityTheory.RgDs.Hilb.hq_w_ne
alias hq_coef_all := PositivityTheory.RgDs.Hilb.hq_coef_all
alias hq_sqInt := PositivityTheory.RgDs.Hilb.hq_sqInt

theorem hilbert_square_integrable_of_signature : StepSig → StepSqInt :=
  PositivityTheory.RgDs.Hilb.hilbert_square_integrable_of_signature

end CompanionTheory.RgDs.Hilb
