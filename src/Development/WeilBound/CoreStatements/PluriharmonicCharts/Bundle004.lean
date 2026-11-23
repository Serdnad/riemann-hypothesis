module

import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle006
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle021
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
public import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.tsg_smul

theorem toWt_inj (Ψ : Type) (N : ℕ) :
    Function.Injective (toWt : MvPolynomial (Ψ × Fin N) ℝ → MvPolynomial (Ψ × Fin N) ℝ) := by
  apply GlobalTheory.CompanionTheory.Ar.Top.FlDeg.toWt_leftInverse_injective <;> assumption

end PositivityTheory.Xgp.tsg_smul

theorem PositivityTheory.Xgp.t_tsg_smul : (∀ (D : ℕ) (κ : ℕ → ℝ) (v : ℝ) (Q : Polynomial ℝ), tsgPoly D κ (Polynomial.C v * Q) = Polynomial.C v * tsgPoly D κ Q) ∧ (∀ (σ : Type) (c : σ → ℝ) (e : σ → ℤ) (v : ℝ) (Q : MvPolynomial σ ℝ), linePoly c e (C v * Q) = Polynomial.C v * linePoly c e Q) ∧ ∀ (Ψ : Type) (N : ℕ), Function.Injective (toWt : MvPolynomial (Ψ × Fin N) ℝ → MvPolynomial (Ψ × Fin N) ℝ) := by
  refine ⟨?_, ?_, fun Ψ N => PositivityTheory.Xgp.tsg_smul.toWt_inj Ψ N⟩
  · intro D κ v Q
    by_cases hv : v = 0
    · subst hv
      simp [tsgPoly]
    · simp only [tsgPoly, Polynomial.natDegree_C_mul hv, Polynomial.coeff_C_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      split_ifs
      · simp only [Polynomial.C_mul]
        ring
      · simp
  · intro σ c e v Q
    simp [linePoly, Polynomial.algebraMap_eq]
end

section

open Matrix
open GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

namespace PositivityTheory.Xgp.GenFam

variable {G : Type} [Field G] {S : Type} {r : S → ℕ}

theorem adjoin_low (F : Type) [Field F] [Algebra F G] (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G)
    (h1 : ∀ s a, u s a a = 1) (h0 : ∀ s a b, a < b → u s a b = 0) :
    IntermediateField.adjoin F (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2) =
      IntermediateField.adjoin F
        (Set.range fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) := by
  refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin.mono _ _ _ ?_)
  · rintro _ ⟨⟨s, a, b⟩, rfl⟩
    show u s a b ∈ IntermediateField.adjoin F _
    rcases lt_trichotomy a b with h | h | h
    · rw [h0 s a b h]; exact zero_mem _
    · rw [h, h1]; exact one_mem _
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨s, (a, b), h⟩, rfl⟩
  · rintro _ ⟨⟨s, ⟨a, b⟩, h⟩, rfl⟩
    exact ⟨⟨s, a, b⟩, rfl⟩

variable {Ω : Type} [Field Ω] [Algebra Ω G]

theorem of_gen [Finite S] {u v : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G} (hu : IsGenFam Ω G u)
    (h1 : ∀ s a, v s a a = 1) (h0 : ∀ s a b, a < b → v s a b = 0)
    (h : ∀ s a b, u s a b ∈
      IntermediateField.adjoin Ω (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => v q.1 q.2.1 q.2.2)) :
    IsGenFam Ω G v := by
  have htop : IntermediateField.adjoin Ω (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => v q.1 q.2.1 q.2.2) = ⊤ := by
    rw [eq_top_iff, ← hu.2.2.2]
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨q, rfl⟩
    exact h _ _ _
  refine ⟨h1, h0, ?_, htop⟩
  rw [adjoin_low Ω v h1 h0] at htop
  haveI : Algebra.IsAlgebraic (Algebra.adjoin Ω (Set.range
      fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2)) G := by
    refine IntermediateField.isAlgebraic_adjoin_iff_top.1 ⟨fun x => ?_⟩
    exact isAlgebraic_algebraMap (⟨x, by rw [htop]; trivial⟩ : IntermediateField.adjoin Ω _)
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite Ω _ hu.2.2.1.cardinalMk_le_trdeg).1

theorem inv_mem {n : ℕ} (F : IntermediateField Ω G) (M : Matrix (Fin n) (Fin n) G) (hd : IsUnit M.det)
    (h : ∀ a b, M a b ∈ F) (a b : Fin n) : M⁻¹ a b ∈ F := by
  let M' : Matrix (Fin n) (Fin n) F := fun a b => ⟨M a b, h a b⟩
  have e : M = M'.map (algebraMap F G) := rfl
  have hd' : IsUnit M'.det := by
    rw [isUnit_iff_ne_zero] at hd ⊢
    intro h0
    apply hd
    rw [e, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have : M⁻¹ = (M'⁻¹).map (algebraMap F G) := by
    apply Matrix.inv_eq_right_inv
    rw [e, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hd', Matrix.map_one _ (map_zero _) (map_one _)]
  rw [this]
  exact (M'⁻¹ a b).2

end PositivityTheory.Xgp.GenFam
end
