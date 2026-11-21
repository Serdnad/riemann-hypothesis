import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.ExplicitFunctionSquareIntegrable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset

namespace CompanionTheory.RgDs

open Finset MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

alias phi := PositivityTheory.RgDs.phi

theorem phi_one {n : ℕ} : phi (1 : Matrix (Fin n) (Fin n) ℂ) = 1 :=
  PositivityTheory.RgDs.phi_one
alias FinVol := PositivityTheory.RgDs.FinVol
alias ExplicitFunctionSquareIntegrable := PositivityTheory.RgDs.ExplicitFunctionSquareIntegrable

end CompanionTheory.RgDs
