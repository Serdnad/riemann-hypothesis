module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.FiniteAdelesSecondCountable
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoAF
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

noncomputable section

namespace PI.VolStabS.TopoAF

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology TopologicalSpace Filter
open scoped RestrictedProduct

variable (F : Type) [Field F] [NumberField F]

instance countable_field : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)

instance countable_ringOfIntegers : Countable (𝓞 F) := Finsupp.Countable.of_moduleFinite (R := ℤ)

theorem countable_ideal : Countable (Ideal (𝓞 F)) := by
  apply _root_.PI.VolStabW.TopoAF.countable_ideal <;> assumption

instance countable_spectrum : Countable (HeightOneSpectrum (𝓞 F)) := by
  have := countable_ideal F
  have hi : Function.Injective (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) :=
    fun v w h => HeightOneSpectrum.ext h
  exact hi.countable

variable {F} in
instance separable_adicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    SeparableSpace (v.adicCompletion F) := by
  let h := (HeightOneSpectrum.adicCompletion.equivCompletion F v).toHomeomorphOfIsInducing
    (HeightOneSpectrum.adicCompletion.isUniformInducing_toCompletion F v).isInducing
  have : Countable (WithVal (v.valuation F)) := (WithVal.equiv (v.valuation F)).injective.countable
  exact h.symm.surjective.denseRange.separableSpace h.symm.continuous

variable {F} in
instance secondCountable_adicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    SecondCountableTopology (v.adicCompletion F) :=
  UniformSpace.secondCountable_of_separable _

theorem isOpen_integers (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  Valued.isOpen_valuationSubring _

instance secondCountable_finiteAdeleRing : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := by
  apply _root_.PI.LevelKSplit.W.SC.finite_adeles_secondCountable <;> assumption

instance secondCountable_adeleRing : SecondCountableTopology (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

section HA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F} {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E]

instance secondCountable_tensAF : SecondCountableTopology (AF F ⊗[F] E) := inferInstance

theorem secondCountable_HA_of (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [SecondCountableTopology R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : SecondCountableTopology (HA R σ J) := by
  apply _root_.PI.VolStabW.TopoAF.secondCountable_HA_of <;> assumption

instance secondCountable_HA (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    SecondCountableTopology (HA (AF F) σ J) :=
  secondCountable_HA_of (AF F) σ J

end HA

end PI.VolStabS.TopoAF
