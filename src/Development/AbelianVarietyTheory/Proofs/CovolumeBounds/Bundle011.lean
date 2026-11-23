module

import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle009
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002

@[expose] public section

section

namespace GlobalTheory.SummablePiProd

universe u_1 u_2

theorem summable_pi_prod {ι : Type u_1} [inst : Fintype ι] {J : ι → Type u_2}
    {u : (i : ι) → J i → ℝ} (h0 : ∀ (i : ι) (j : J i), (0 : ℝ) ≤ u i j)
    (hs : ∀ (i : ι), Summable (u i)) :
    Summable fun (t : (i : ι) → J i) ↦ ∏ i : ι, u i (t i) := by
  apply GlobalTheory.summable_pi_prod_of_nonneg <;> assumption

end GlobalTheory.SummablePiProd
end

section

open Filter Topology

namespace GlobalTheory

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem norm_pderivIter_le_of_nonneg {F : (ι → ℂ) → V} {U : Set (ι → ℂ)} {a : ι → ℂ} {r : ι → ℝ}
    {M : ℝ} (α : ι →₀ ℕ) (hr : ∀ k, 0 ≤ r k) (hα : ∀ k, α k ≠ 0 → 0 < r k) (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) (hsub : ∀ z : ι → ℂ, (∀ k, ‖z k - a k‖ ≤ r k) → z ∈ U)
    (hM : ∀ z : ι → ℂ, (∀ k, ‖z k - a k‖ = r k) → ‖F z‖ ≤ M) :
    ‖pderivIter α F a‖ ≤ (∏ k, ((α k).factorial : ℝ)) * M / ∏ k, r k ^ α k :=
  norm_pderivIter_le_of_analyticAt α hr hα
    (fun z hz => SCV.analyticOnNhd_of_differentiableOn hU hF z (hsub z hz)) hM

theorem norm_pderivIter_le_of_differentiable {F : (ι → ℂ) → V} {a : ι → ℂ} {r : ι → ℝ} {M : ℝ}
    (α : ι →₀ ℕ) (hr : ∀ k, 0 ≤ r k) (hα : ∀ k, α k ≠ 0 → 0 < r k) (hF : Differentiable ℂ F)
    (hM : ∀ z : ι → ℂ, (∀ k, ‖z k - a k‖ = r k) → ‖F z‖ ≤ M) :
    ‖pderivIter α F a‖ ≤ (∏ k, ((α k).factorial : ℝ)) * M / ∏ k, r k ^ α k :=
  norm_pderivIter_le_of_nonneg α hr hα isOpen_univ hF.differentiableOn
    (fun _ _ => Set.mem_univ _) hM

section Holomorphic

variable {F G : (ι → ℂ) → V} {U : Set (ι → ℂ)} {a : ι → ℂ}

end Holomorphic

end GlobalTheory
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG IsProjOver)
namespace GlobalTheory.ProjSpace

private lemma isClosedEmbedding_sigma_desc_of_pairwise_disjoint_range {ι : Type} [Finite ι] {Z : ι → Type*}
    [∀ i, TopologicalSpace (Z i)] {W : Type*} [TopologicalSpace W] (g : ∀ i, Z i → W)
    (hg : ∀ i, Topology.IsClosedEmbedding (g i))
    (h : Pairwise fun i j => Disjoint (Set.range (g i)) (Set.range (g j))) :
    Topology.IsClosedEmbedding (fun p : Σ i, Z i => g p.1 p.2) := by
  refine .of_continuous_injective_isClosedMap ?_ ?_ ?_
  · exact continuous_sigma fun i => (hg i).continuous
  · rintro ⟨i, x⟩ ⟨j, y⟩ hxy
    by_cases hij : i = j
    · subst hij
      obtain rfl := (hg i).injective hxy
      rfl
    · exact absurd hxy ((h hij).ne_of_mem ⟨x, rfl⟩ ⟨y, rfl⟩)
  · intro C hC
    have hC' : (fun p : Σ i, Z i => g p.1 p.2) '' C = ⋃ i, g i '' (_root_.Sigma.mk i ⁻¹' C) := by
      ext w
      simp
    rw [hC']
    exact isClosed_iUnion_of_finite fun i => (hg i).isClosedMap _ (hC.preimage continuous_sigmaMk)


open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial in
theorem _root_.GlobalTheory.ProjSpace.isClosedImmersion_sigmaDesc {ι : Type} [Finite ι]
    {X : ι → Scheme.{0}} {Y : Scheme.{0}}
    (f : ∀ i, X i ⟶ Y) (hf : ∀ i, IsClosedImmersion (f i))
    (h : Pairwise fun i j => Disjoint (Set.range (f i)) (Set.range (f j))) :
    IsClosedImmersion (Sigma.desc f) := by
  have hsurj : SurjectiveOnStalks (Sigma.desc f) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @SurjectiveOnStalks) fun i => (hf i).toSurjectiveOnStalks
  have key : ⇑(Sigma.desc f) ∘ AlgebraicGeometry.sigmaMk X = fun p => f p.1 p.2 := by
    funext ⟨i, x⟩
    rw [Function.comp_apply, AlgebraicGeometry.sigmaMk_mk, ← Scheme.Hom.comp_apply, Sigma.ι_desc]
  have hce : Topology.IsClosedEmbedding (Sigma.desc f) := by
    have e := isClosedEmbedding_sigma_desc_of_pairwise_disjoint_range (fun i => ⇑(f i))
      (fun i => (hf i).isClosedEmbedding) h
    rw [← key] at e
    have hsplit : ⇑(Sigma.desc f) =
        (⇑(Sigma.desc f) ∘ AlgebraicGeometry.sigmaMk X) ∘ (AlgebraicGeometry.sigmaMk X).symm := by
      funext y
      simp
    rw [hsplit]
    exact e.comp (AlgebraicGeometry.sigmaMk X).symm.isClosedEmbedding
  haveI : IsPreimmersion (Sigma.desc f) := (isPreimmersion_iff _).2 ⟨hsurj, hce.isEmbedding⟩
  exact .of_isPreimmersion _ hce.isClosed_range

end GlobalTheory.ProjSpace
end
end
