module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.LeftInv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FibreFactorHolds
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.NewtonLow

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.RgJS

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def locT (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) (w.adicCompletion E)) : Module.End ℂ (Sm E n) :=
  finRep E n (locGL E n w g)

def FixAt (w : HeightOneSpectrum (𝓞 E)) (f : Sm E n) : Prop := ∀ k ∈ GlobalTheory.LFun.KGL w (n := n), locT w k f = f

def InKgK (w : HeightOneSpectrum (𝓞 E)) (g y : GL (Fin n) (w.adicCompletion E)) : Prop :=
  ∃ k₁ ∈ GlobalTheory.LFun.KGL w (n := n), ∃ k₂ ∈ GlobalTheory.LFun.KGL w (n := n), y = k₁ * g * k₂

def IsHk (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) (w.adicCompletion E)) (R : Finset (GL (Fin n) (w.adicCompletion E))) :
    Prop :=
  (∀ r ∈ R, InKgK w g r) ∧ ∀ y, InKgK w g y → ∃! r, r ∈ R ∧ r⁻¹ * y ∈ GlobalTheory.LFun.KGL w (n := n)

def hk (w : HeightOneSpectrum (𝓞 E)) (R : Finset (GL (Fin n) (w.adicCompletion E))) : Module.End ℂ (Sm E n) :=
  ∑ r ∈ R, locT w r

end Defs

end DiscreteGroups.T1.G

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem twtr_cont_of_mem (π : CuspSub E n) {ψ : Sm E n} (hψ : ψ ∈ π.V) : Continuous ψ.1 :=
  GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E n ψ (π.cusp ψ hψ).1.level

theorem twtr_integrable (μ : Measure (H E n 0)) [IsLocallyFiniteMeasure μ] {φ : H E n 0 → ℂ} (hφ : IsTestH φ)
    {f : GA E n → ℂ} (hf : Continuous f) (x : GA E n) :
    Integrable (fun y : H E n 0 => φ y * f (x * y.1)) μ := by
  have : BorelSpace (H E n 0) := ⟨rfl⟩
  have : IsFiniteMeasureOnCompacts μ :=
    ⟨fun K hK => hK.measure_lt_top_of_nhdsWithin fun x _ => μ.finiteAt_nhdsWithin x K⟩
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact hφ.1.mul (hf.comp (continuous_const.mul continuous_fst))
  · exact hφ.2.mul_right

end

end DiscreteGroups.T1.G

end
end
