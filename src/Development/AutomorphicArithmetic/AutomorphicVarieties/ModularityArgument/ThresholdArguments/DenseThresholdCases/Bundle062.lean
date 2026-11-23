module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle002
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle009
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SmoothRepIrreducibleSubcontainingVector
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TensorProductVectors
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypeData
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FlagPol
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle061
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.FixedDvd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevFixedSs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle060
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section




section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix UpperTheory.TNZ
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.NonzeroTypeTheory
theorem nz_of_steps_alt (P : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (k2 : SmoothRepIrreducibleSubcontainingVector) (k3 : SmoothRepMinimalSubrepresentation) (k4 : SchurInjectiveFromIrreducible) (a1 : ArtinTransferDecompositionCharacter) (a3 : LocalArtinCharacterProduct)
    (a4 : FiniteDimensionalTranslationCoordinates) (a5 : TwistedSphericalRepresentative) (a6 : DistinctOnUnitsDistinctOnInertia) (a7 : SmoothVectorsFixedByCongruence) (gm : _root_.UpperTheory.TNZ.GMainAlt) (ge : GEmb) (gi : ArtinInertiaProp)
    (cm : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → Need_CMain) (cp : Need_CProps) (gr : Need_Grp) : _root_.UpperTheory.NonzeroTypeTheory.NonzeroTypes :=
  _root_.UpperTheory.NonzeroTypeTheory.nz_of_typeData_alt k2 k3 k4 (_root_.UpperTheory.V.Z.Win.T2.typeData_alt P a1 a3 a4 a5 a6 a7 gm ge gi cm cp gr)
end UpperTheory.NonzeroTypeTheory
end
end
end

section




section
theorem UpperTheory.V.Lev.fixedSs_of_prints (P : _root_.UpperTheory.V.Af.Hypotheses') : _root_.UpperTheory.V.Lev.FixedSsAlt :=
  _root_.UpperTheory.V.Lev.fixed_semisimple_of_flag_fixed_dvd_fixed_unramified UpperTheory.V.Lev.flagPol (_root_.UpperTheory.V.Z.Win.T2.fixedDvd' P) (_root_.UpperTheory.V.Z.Win.T2.fixedUnr_alt P)
end
end

section

noncomputable abbrev UpperTheory.Zero.LLC.IsRecT.langlandsQuotientDense := @UpperTheory.V.Z.Win.T2.lQuot_alt
end
