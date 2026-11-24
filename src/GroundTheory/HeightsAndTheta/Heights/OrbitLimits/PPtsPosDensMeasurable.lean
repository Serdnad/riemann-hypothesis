module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsPosDensMeasurable
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsPosDensMeasurable
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsSumMeasurableA
import Mathlib.Topology.Separation.CompletelyRegular
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheetA

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

theorem PtsPosDensMeasurable.proof : PtsPosDensMeasurable.Statement := by
  intro K _ ι _ P e Ψ L g hP hΨ hL hg hdeg
  exact (PtsPosDens.aestronglyMeasurable_of_measurable_weight hP hΨ hL hg hdeg).aemeasurable

end GroundTheory.Heights₂.Heights
