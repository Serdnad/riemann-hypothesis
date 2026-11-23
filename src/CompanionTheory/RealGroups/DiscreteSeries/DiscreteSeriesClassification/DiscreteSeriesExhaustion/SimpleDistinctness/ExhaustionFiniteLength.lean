module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.Development
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ContinuousUnitsRenSymm
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsIsoOfHighest
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsPermOfCapPEq
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle030
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle049
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KHighestOfPerm
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle048
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle064
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle015
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle065
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle057
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle029
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle014

@[expose] public section

namespace CompanionTheory.RgExh.Fin

theorem exhaustion_finite_length : CompanionTheory.RgExh.Finish :=
  GlobalTheory.CompanionTheory.RgExhFin.finish
    GlobalTheory.CompanionTheory.RgStart.startMod
    GlobalTheory.CompanionTheory.RgSteps.pathFin
    GlobalTheory.CompanionTheory.RgPath.pathExists
    GlobalTheory.CompanionTheory.RgPath.pathEndNat
    GlobalTheory.CompanionTheory.RgExhFin.simpleDistinct
    GlobalTheory.CompanionTheory.AdjointSignNormality.scalar_of_separating_smooth_l2_maps
    GlobalTheory.CompanionTheory.RgExhFin.unitarizable_of_separating_smooth_l2_maps
    GlobalTheory.CompanionTheory.RgIso.isoFacts
    GlobalTheory.CompanionTheory.CharOfLowK.charOfAlgDS
    GlobalTheory.CompanionTheory.LowestDataIso.algUniq
    GlobalTheory.CompanionTheory.LowestData.dataUniq
    GlobalTheory.CompanionTheory.RenumDS.dsOfArr
    GlobalTheory.CompanionTheory.DSData.dsOfData
    GlobalTheory.CompanionTheory.KModOfStep.kModOf
    GlobalTheory.CompanionTheory.ArrCount.arrCount

end CompanionTheory.RgExh.Fin
