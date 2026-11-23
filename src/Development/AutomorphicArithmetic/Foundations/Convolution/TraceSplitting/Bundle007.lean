module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.Bundle002
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.IsoEq
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.NormCharPowHolds
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
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

@[expose] public section

section

open NumberField in
private theorem not_both (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)

open NumberField in
theorem UpperTheory.ConvolutionTheory.T.cbcc :
    UpperTheory.ConvolutionTheory.T.Places → UpperTheory.ConvolutionTheory.T.LiftStep → UpperTheory.ConvolutionTheory.T.LiftAll → UpperTheory.ConvolutionTheory.T.DescStep → UpperTheory.ConvolutionTheory.T.SplitStrong → UpperTheory.V.Z.Bc.CBCc := by
  intro hPl hLS hLA hDS hSS K M _ _ _ _ _ _ hp hK n hn
  haveI := hK
  haveI hM : IsTotallyComplex M := isTotallyComplex_of_algebra K M
  haveI : Fact (Module.finrank K M).Prime := ⟨hp⟩
  haveI : FiniteDimensional K M := Module.finite_of_finrank_pos hp.pos
  haveI : IsCyclic (M ≃ₐ[K] M) := isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank K M)
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := M ≃ₐ[K] M)
  refine ⟨fun π => ?_, fun P hP => ?_, fun π P _ hw => UpperTheory.ConvolutionTheory.R.fibre_holds K M hp n hn π P hw⟩
  · rcases π with @⟨_, π⟩ | @⟨hR, π⟩
    swap
    · exact (not_both K hR hK).elim
    rcases hLS K M σ hσ hp n hn (fun m hm _ => hLA K M σ hσ hp m hm) π with ⟨ι, _, m, Q, hm, h2, hw⟩ | ⟨P, ⟨h1, h2⟩, h3⟩
    · obtain ⟨η, hη, e⟩ := UpperTheory.ConvolutionTheory.R.twoParts_holds K M hp n _ ι m Q hn hm h2 hw
      exact Or.inl ⟨η, hη, Quotient.exact e⟩
    · exact Or.inr ⟨.cx P, h1, fun τ m h => (h2 τ m).1 h, hSS K M σ hσ hp n hn π P h3 h1⟩
  · rcases P with @⟨_, P⟩ | @⟨hR, P⟩
    swap
    · exact (not_both M hR hM).elim
    obtain ⟨hinf, -, hne, -⟩ := hPl K M hp
    obtain ⟨v, hv⟩ := hinf.nonempty
    obtain ⟨w⟩ := hne v
    obtain ⟨π, ⟨h1, h2⟩, -⟩ := hDS K M σ hσ hp n hn P hP v w hv
    exact ⟨.cx π, h1, fun τ m h => (h2 τ m).2 h, hSS K M σ hσ hp n hn π P hP h1⟩
end

section

theorem UpperTheory.ConvolutionTheory.T.splitStrong :
    UpperTheory.ConvolutionTheory.T.DescStep → UpperTheory.ConvolutionTheory.T.SplitStrong := by
  intro hD F E _ _ _ _ _ _ _ _ σ hσ hp n hn π P hc hw v w i hi hcomp τ τ' hτ hτ'
  obtain ⟨-, -, -, -, -, hpl⟩ := UpperTheory.ConvolutionTheory.T.places F E hp
  obtain ⟨hs, u, rfl, hiu⟩ := hpl v w i hi hcomp
  obtain ⟨π', hl, hloc⟩ := hD F E σ hσ hp n hn P hc v u hs
  obtain ⟨η, hη, hiso⟩ := (UpperTheory.ConvolutionTheory.R.fibre_holds F E hp n hn (.cx π') (.cx P) hl.1).2 (.cx π) hw
  have he : π'.twist η = π := (UpperTheory.ConvolutionTheory.Dp.isoEq F n (π'.twist η) π).1 hiso
  subst he
  have hτ₀ : (UpperTheory.CBC.Cusp.cx π').locComp v τ := by
    rcases hη with rfl | hη
    · simpa [GlobalTheory.CuspRep.CuspSub.twist_one] using hτ
    · exact (UpperTheory.ConvolutionTheory.T.normCharSplit F E σ hσ hp n hn η hη v hs π' τ).1 hτ
  obtain ⟨e, he⟩ := hloc τ τ' hτ₀ hτ'
  have hm : i.toRingHom = GroundTheory.Global.SemiLocal.completionMap v u.1 := RingHom.ext hiu
  refine ⟨e, fun g x => ?_⟩
  rw [hm]
  exact he g x
end
