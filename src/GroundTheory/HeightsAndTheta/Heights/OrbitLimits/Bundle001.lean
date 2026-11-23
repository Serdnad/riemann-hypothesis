module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MeasureTheory

def CovolumeRelIndex.Statement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (L₁ L₂ : Submodule ℤ E) [DiscreteTopology L₁]
    [IsZLattice ℝ L₁] [DiscreteTopology L₂] [IsZLattice ℝ L₂], L₁ ≤ L₂ →
      ZLattice.covolume L₁ μ = (L₁.toAddSubgroup.relIndex L₂.toAddSubgroup : ℝ) * ZLattice.covolume L₂ μ

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MeasureTheory
open scoped ENNReal

def LatticeCountVolume.Statement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (La : Submodule ℤ E) [DiscreteTopology La]
    [IsZLattice ℝ La] (S T : Set E), MeasurableSet S → (∀ x ∈ S, ∀ y ∈ S, x - y ∈ T) →
      μ S ≤ (({x : E | x ∈ La ∧ x ∈ T}.encard : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (ZLattice.covolume La μ)

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding


open scoped Classical in
def MixedBoxCount.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (La : Submodule ℤ (mixedSpace F)) [DiscreteTopology La]
    [IsZLattice ℝ (E := mixedSpace F) La] (f : InfinitePlace F → ℝ), (∀ w, 0 < f w) →
      {y : mixedSpace F | y ∈ La ∧ ∀ w, normAtPlace w y ≤ f w}.Finite ∧
        Real.log (convexBodyLTFactor F : ℝ) + ∑ w, (mult w : ℝ) * Real.log (f w) -
            Module.finrank ℚ F * Real.log 2 - Real.log (ZLattice.covolume La) ≤
          Real.log ({y : mixedSpace F | y ∈ La ∧ ∀ w, normAtPlace w y ≤ f w}.ncard : ℝ)

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

def CriticalFibreInfinite.Statement : Prop :=
  ∀ (k d : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin d → ℂ),
    IsOpen U → U.Nonempty → DifferentiableOn ℂ f U →
      (∀ t ∈ U, ¬ Function.Injective (fderiv ℂ f t)) →
        ∃ y : Fin d → ℂ, {t | t ∈ U ∧ f t = y}.Infinite

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.mixedEmbedding

noncomputable def latticeImage (F : Type*) [Field F] (L : AddSubgroup F) : Submodule ℤ (mixedSpace F) :=
  (L.map (mixedEmbedding F).toAddMonoidHom).toIntSubmodule

theorem mem_latticeImage {F : Type*} [Field F] (L : AddSubgroup F) (y : mixedSpace F) :
    y ∈ latticeImage F L ↔ ∃ x ∈ L, mixedEmbedding F x = y := by
  change y ∈ L.map (mixedEmbedding F).toAddMonoidHom ↔ _
  simp


open scoped Classical in
def LatticeImageZLattice.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (L : AddSubgroup F), L.FG →
    (∀ x : F, ∃ n : ℕ, 0 < n ∧ (n : F) * x ∈ L) →
      ∃ _ : DiscreteTopology (latticeImage F L), IsZLattice ℝ (E := mixedSpace F) (latticeImage F L)

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.InfinitePlace

def EmbeddingSumPlaces.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (g : (F →+* ℂ) → ℝ),
    (∀ σ, g (ComplexEmbedding.conjugate σ) = g σ) →
      ∑ σ : F →+* ℂ, g σ = ∑ w : InfinitePlace F, (mult w : ℝ) * g w.embedding

end GroundTheory.Heights₂.Heights.Targets
end
