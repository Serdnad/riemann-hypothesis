module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
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
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
public import Mathlib.Analysis.Calculus.FDeriv.Congr

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def RegularInjectivePieces.Statement : Prop :=
  ∀ (d : ℕ) (U : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → Fin d → ℂ), IsOpen U → DifferentiableOn ℂ g U →
    ∃ P : ℕ → Set (Fin d → ℂ), (∀ i, MeasurableSet (P i)) ∧ Pairwise (Function.onFun Disjoint P) ∧
      ⋃ i, P i = {w | w ∈ U ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} ∧
      ∀ i, Set.InjOn g (P i)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def ReducedNormalisationPlace.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsReduced R] [IsNoetherianRing R]
    (P : MaximalSpectrum (integralClosure R (FractionRing R))),
    ∃ p ∈ minimalPrimes R, ∀ (S : Type) [CommRing S] (φ : R →+* S),
      Function.Surjective φ → RingHom.ker φ = p →
        ∃ P' : MaximalSpectrum (integralClosure S (FractionRing S)), ∀ x : R,
          Ring.ord (Localization.AtPrime P.asIdeal)
              (algebraMap (integralClosure R (FractionRing R)) (Localization.AtPrime P.asIdeal)
                (algebraMap R (integralClosure R (FractionRing R)) x)) =
            Ring.ord (Localization.AtPrime P'.asIdeal)
              (algebraMap (integralClosure S (FractionRing S)) (Localization.AtPrime P'.asIdeal)
                (algebraMap S (integralClosure S (FractionRing S)) (φ x)))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology ComplexSets
open scoped ContDiff Matrix

noncomputable section

theorem maDens_congr {D : ℕ} {F G : Fin D → (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : ∀ k, F k =ᶠ[𝓝 z] G k) : ReciprocityTheory.AnForm.maDens F z = ReciprocityTheory.AnForm.maDens G z := by
  have h2 : ∀ k, fderiv ℝ (fderiv ℝ (F k)) z = fderiv ℝ (fderiv ℝ (G k)) z :=
    fun k => ((h k).fderiv (𝕜 := ℝ)).fderiv_eq
  have h3 : (fun k => ReciprocityTheory.AnForm.hessC (F k) z) = fun k => ReciprocityTheory.AnForm.hessC (G k) z := by
    funext k
    ext i j
    dsimp only [ReciprocityTheory.AnForm.hessC]
    rw [h2 k]
  unfold ReciprocityTheory.AnForm.maDens
  rw [h3]

end

end GroundTheory.Heights₂.Heights
end
