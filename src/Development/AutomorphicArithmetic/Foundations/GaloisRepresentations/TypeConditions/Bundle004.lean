module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle093
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.RhoBar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011

@[expose] public section

section

noncomputable section

namespace UpperTheory.GalS

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory GlobalTheory.StringRepresentationDecomposition UpperTheory.GalC

theorem g2g' {D : D7} (h : DeRhamJumpsDistinctCondition D) : ∀ i r, GoodR D.nd i r → (D.nd.l i = D.host.g 0 ∨ D.nd.l i = D.host.g 1) →
    ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ x, D.naut.IsdRW i (AdmissibleParameterJ.rQ D i r x) w ∧
      ∀ τ₀, InducesW D.nd i τ₀ w → D.naut.jumpsW i (AdmissibleParameterJ.rQ D i r x) τ₀ = D.naut.locAutHodgeTateWeightsLevelZero i τ₀ := h.1

theorem jc_of_u {D : D7} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))} (hr : GoodR D.nd i r)
    (hS : GlobalTheory.SplitCoef.OSplit D) (h : DistinctAbsIrredConstituents D.nd i r) : AbsIrreducibleDistinct D i r := by
  obtain ⟨K', hK', hA, _, hK⟩ := h
  exact GlobalTheory.T.absIrr_distinct_constituents_after_extension D i r (hS i) hr K' (algebraMap (Kf D.nd i) K') (fun x => (hK x).2)

end UpperTheory.GalS
end
end

section

noncomputable section

section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem UpperTheory.GalS.jointCondition_of_constituentCondition_split (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : GoodR D.nd i r) (h : UpperTheory.GalS.DistinctAbsIrredConstituents D.nd i r) (hS : GlobalTheory.SplitCoef.OSplitAt D i) : AbsIrreducibleDistinct D i r := by
  obtain ⟨K', hK', hA, _, hK⟩ := h
  exact GlobalTheory.T.absIrr_distinct_constituents_after_extension D i r hS hr K' (algebraMap (Kf D.nd i) K') (fun x => (hK x).2)
end

section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory.CrysFromGTwo

end GlobalTheory.CrysFromGTwo
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.DualTwistCrys

end GlobalTheory.DualTwistCrys
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.CrysChiOne
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)}

end GlobalTheory.CrysChiOne
end

section
namespace Formalism.MainNotions.N
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open NumberField IsDedekindDomain

end Formalism.MainNotions.N
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices
namespace GlobalTheory.AbsoluteIrreducibilityOfTraceSpan

end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

end
end
end
