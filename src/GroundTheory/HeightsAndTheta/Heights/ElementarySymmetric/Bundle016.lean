module

public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle007
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.IsMultiHomogChartMonomial
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle054
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDegLTGrowth
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEventualPolynomial
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFiltrationHilbSum
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle046
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertPrime
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedNumberPolynomial
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PModulesFromPrimes
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultigradedFiltration
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle091
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle079
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionNormSqExtension
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)]

theorem MuFrameExists.proof (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D) :
    MuFrameExists.Statement D H := by
  intro z hz
  choose c hc using hz.1
  have hx : segreCoord D.y c ≠ 0 := HermMetricEq.segreCoord_ne_zero hz hc
  obtain ⟨m, f, cc, hf, hcc, hsum, hdat⟩ := H.locally c hx
  choose vf hvf using fun l =>
    IndefiniteRowSideFullHecke.LowerBoundFree.regularAt_of_mem_chartRing hz hc (hf l)
  choose vc hvc using fun l =>
    IndefiniteRowSideFullHecke.LowerBoundFree.regularAt_of_mem_chartRing hz hc (hcc l)
  have hS : IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt D.y (∑ l, cc l * f l) z (∑ l, vc l * vf l) :=
    IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt.sum _ fun l _ => (hvc l).mul (hvf l)
  rw [hsum] at hS
  have h1 : (∑ l, vc l * vf l) = 1 :=
    IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt.unique hz hS IndefiniteRowSideFullHecke.LowerBoundFree.isValueAt_one
  have hex : ∃ l, vf l ≠ 0 := by
    by_contra hne
    simp only [not_exists, not_not] at hne
    simp [hne] at h1
  obtain ⟨l, hl⟩ := hex
  obtain ⟨b, hb, u, hu, heq⟩ := hdat l
  exact ⟨⟨c, f l, ⟨hc, vf l, HermMetricEq.isValueAt_iff.2 (hvf l), hl⟩, b, hb, u, hu, heq⟩⟩

end GroundTheory.Heights₂.Heights.NineStatements
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Swarm

open GroundTheory.Heights₂.Heights.HilbertSamuel

theorem HilbertPrime.closed : HilbertPrime.Statement.{0} :=
  HilbertPrime.proof HilbertDimZero.proof (HilbertIncrement.proof IntersectionRecursion.proof)
    (MixedNumberPolynomial.proof (MultigradedHilbertPolynomial.proof EventualPolynomial.proof))
    (ModulesFromPrimes.proof MultigradedFiltration.proof FiltrationHilbSum.proof DegLTGrowth.proof)

theorem RankOfSections.closed : RankOfSections.Statement :=
  RankOfSections.proof HilbertPrime.closed
    (MixedNumberPolynomial.proof (MultigradedHilbertPolynomial.proof EventualPolynomial.proof))

theorem ProjDegGenDeg.proof : ProjDegGenDeg.Statement :=
  HilbertSamuel.ProjDegGenDeg.proof RankOfSections.closed

end GroundTheory.Heights₂.Heights.Swarm
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem SectionNormSqExtension.closed : SectionNormSqExtension.Statement :=
  SectionNormSqExtension.proof LeviLogFlat.proof LeviHolPerturb.proof LeviCompHol.proof LeviFSInvariant.proof

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree Filter Topology
open ReciprocityTheory.AnForm.M (IsCompatChart)

def ProjChartHolo.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (M : XModel D)
    (e : OpenPartialHomeomorph M.Xc (Fin D.n → ℂ)), IsCompatChart M.atlas e →
    ∀ γ : ℂ → (Σ k, ι k) → ℂ, AnalyticAt ℂ γ 0 → (∀ᶠ s in 𝓝 (0 : ℂ), γ s ∈ mcPts (mCoordIdeal D.y)) →
      M.proj (γ 0) ∈ e.source → AnalyticAt ℂ (fun s => e (M.proj (γ s))) 0

end GroundTheory.Heights₂.Heights.NineStatements
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree Filter Topology

def RefChartDisc.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D) (M : XModel D)
    (S : LogLogRegularisationSetting M D.Xo (muLine H)) (k : Fin S.R.N) (γ : ℂ → (Σ k, ι k) → ℂ), AnalyticAt ℂ γ 0 →
    (∀ᶠ s in 𝓝 (0 : ℂ), γ s ∈ mcPts (mCoordIdeal D.y)) → M.proj (γ 0) ∈ (S.R.chart k).source →
      ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧ ∀ᶠ s in 𝓝 (0 : ℂ),
        Real.log (S.ref.h (γ s)) = S.R.q k (S.R.chart k (M.proj (γ s))) - (G s).re

end GroundTheory.Heights₂.Heights.NineStatements
end
end
