module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle043
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle044
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle045
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle042
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle047
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle034
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle006

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

theorem eq_zero_of_mem_closure_of_continuousAt {σ : Type} [Fintype σ] {k : (σ → ℂ) → ℂ}
    {S : Set (σ → ℂ)} {u : σ → ℂ} (hk : ContinuousAt k u) (hu : u ∈ closure S)
    (h0 : ∀ y ∈ S, k y = 0) : k u = 0 := by
  have h1 := hk.continuousWithinAt.mem_closure_image hu
  have h2 : k '' S ⊆ {0} := by
    rintro _ ⟨y, hy, rfl⟩
    exact h0 y hy
  have h3 := closure_mono h2 h1
  rwa [closure_singleton, Set.mem_singleton_iff] at h3

theorem NormalGermIrreducible.proof (hreg : RegularLocusIdentity.Statement)
    (hext : NormalRiemannExtensionLocal.Statement) (hvan : VanishNearPoint.Statement) :
    NormalGermIrreducible.Statement := by
  classical
  intro σ _ I w hI hnorm hw
  refine ⟨hw, fun f g hf hg hfg => ?_⟩
  set X := zeroSetIn I with hX
  obtain ⟨h, hhI, hid⟩ := hreg σ I hI

  set U : Set (σ → ℂ) := {z | AnalyticAt ℂ f z} ∩ {z | AnalyticAt ℂ g z} ∩
    {z | ∀ᶠ y in 𝓝 z, y ∈ X → f y * g y = 0} with hUdef
  have hUo : IsOpen U :=
    (isOpen_analyticAt ℂ f).inter (isOpen_analyticAt ℂ g) |>.inter isOpen_setOfPred_eventually_nhds
  have hwU : w ∈ U := ⟨⟨hf, hg⟩, hfg⟩

  set E : (σ → ℂ) → Prop := fun z => ∀ᶠ y in 𝓝 z, y ∈ X → f y = 0 with hE

  have key : ∀ z ∈ X ∩ U, eval z h ≠ 0 → ∃ V : Set (σ → ℂ), IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
      ((∀ u ∈ X ∩ V, E u) ∨ (∀ u ∈ X ∩ V, ¬ E u ∧ g u = 0)) := by
    rintro z ⟨hzX, hzU⟩ hhz
    obtain ⟨V, hVo, hzV, hVU, hVid⟩ := hid z hzX hhz U (hUo.mem_nhds hzU)
    refine ⟨V, hVo, hzV, hVU, ?_⟩
    have hfV : AnalyticOnNhd ℂ f V := fun y hy => (hVU hy).1.1
    have hgV : AnalyticOnNhd ℂ g V := fun y hy => (hVU hy).1.2
    by_cases hA : ∃ y ∈ X ∩ V, E y
    · left
      have hf0 := hVid f hfV hA
      intro u hu
      filter_upwards [hVo.mem_nhds hu.2] with y hyV hyX using hf0 y ⟨hyX, hyV⟩
    · right
      push Not at hA
      have hnz : ¬ E z := hA z ⟨hzX, hzV⟩
      have hfr : ∃ᶠ y in 𝓝 z, y ∈ X ∧ f y ≠ 0 := by
        rw [Filter.not_eventually] at hnz
        refine hnz.mono fun y hy => ?_
        by_contra hc
        exact hy fun hyX => by_contra fun hne => hc ⟨hyX, hne⟩
      obtain ⟨y, ⟨hyX, hfy⟩, hyV⟩ := (hfr.and_eventually (hVo.mem_nhds hzV)).exists
      have hg0 : ∀ᶠ u in 𝓝 y, u ∈ X → g u = 0 := by
        filter_upwards [(hVU hyV).2, (hfV y hyV).continuousAt.eventually_ne hfy] with u hu hfu huX
        exact (mul_eq_zero.1 (hu huX)).resolve_left hfu
      have hg0V := hVid g hgV ⟨y, ⟨hyX, hyV⟩, hg0⟩
      exact fun u hu => ⟨hA u hu, hg0V u hu⟩

  set φ : (σ → ℂ) → ℂ := fun z => if E z then 0 else 1 with hφ
  set S := (X ∩ U) \ {z | eval z h = 0} with hS
  have hφhol : HolomorphicOnSubset φ S := by
    rintro z ⟨hzXU, hhz⟩
    obtain ⟨V, hVo, hzV, -, hcase⟩ := key z hzXU hhz
    refine ⟨V, hVo, hzV, ?_⟩
    rcases hcase with h0 | h1
    · refine ⟨fun _ => 0, differentiableOn_const _, fun u hu => ?_⟩
      simp only [hφ, if_pos (h0 u ⟨hu.1.1.1, hu.2⟩)]
    · refine ⟨fun _ => 1, differentiableOn_const _, fun u hu => ?_⟩
      simp only [hφ, if_neg (h1 u ⟨hu.1.1.1, hu.2⟩).1]
  have hφb : Bornology.IsBounded (φ '' S) := by
    refine ((Set.finite_singleton (1 : ℂ)).insert 0).isBounded.subset ?_
    rintro _ ⟨z, -, rfl⟩
    by_cases hz : E z
    · simp [hφ, hz]
    · simp [hφ, hz]
  obtain ⟨V, hVo, hwV, hVU, F, hFd, hFeq⟩ :=
    hext σ I h w U φ hI hnorm hhI hw (hUo.mem_nhds hwU) hφhol hφb

  set N := V ∩ F ⁻¹' Metric.ball (F w) (1 / 2) with hN
  have hNo : IsOpen N := hFd.continuousOn.isOpen_inter_preimage hVo Metric.isOpen_ball
  have hwN : w ∈ N := ⟨hwV, Set.mem_preimage.mpr (Metric.mem_ball_self (by norm_num))⟩
  have hdense := zeroSetIn_subset_closure_diff hvan I h hI hhI

  have spread : ∀ k : (σ → ℂ) → ℂ, (∀ y ∈ U, ContinuousAt k y) →
      (∀ y ∈ X ∩ N, eval y h ≠ 0 → k y = 0) → ∀ᶠ u in 𝓝 w, u ∈ X → k u = 0 := by
    intro k hk h0
    filter_upwards [hNo.mem_nhds hwN] with u huN huX
    have hcl : u ∈ closure (N ∩ (X \ {z | eval z h = 0})) := hNo.inter_closure ⟨huN, hdense huX⟩
    exact eq_zero_of_mem_closure_of_continuousAt (hk u (hVU huN.1)) hcl
      fun y hy => h0 y ⟨hy.2.1, hy.1⟩ hy.2.2
  have hφN : ∀ y ∈ X ∩ N, eval y h ≠ 0 → ‖φ y - F w‖ < 1 / 2 := by
    rintro y ⟨hyX, hyV, hyF⟩ hhy
    rw [← hFeq ⟨⟨hyX, hyV⟩, hhy⟩]
    simpa [dist_eq_norm] using hyF
  by_cases hc : ‖F w‖ < 1 / 2
  · left
    refine spread f (fun y hy => hy.1.1.continuousAt) fun y hy hhy => ?_
    have hEy : E y := by
      by_contra hnE
      have h1 := hφN y hy hhy
      simp only [hφ, if_neg hnE] at h1
      have : ‖(1 : ℂ)‖ < 1 := by
        calc ‖(1 : ℂ)‖ = ‖(1 - F w) + F w‖ := by ring_nf
          _ ≤ ‖1 - F w‖ + ‖F w‖ := norm_add_le _ _
          _ < 1 / 2 + 1 / 2 := add_lt_add h1 hc
          _ = 1 := by norm_num
      simp at this
    exact hEy.self_of_nhds hy.1
  · right
    refine spread g (fun y hy => hy.1.2.continuousAt) fun y hy hhy => ?_
    have hnE : ¬ E y := by
      intro hEy
      have h1 := hφN y hy hhy
      simp only [hφ, if_pos hEy, zero_sub, norm_neg] at h1
      exact hc h1
    obtain ⟨V', -, hyV', -, hcase⟩ := key y ⟨hy.1, hVU hy.2.1⟩ hhy
    rcases hcase with h0 | h1
    · exact absurd (h0 y ⟨hy.1, hyV'⟩) hnE
    · exact (h1 y ⟨hy.1, hyV'⟩).2

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

theorem BranchInverseHolomorphic.proof (hdim : BranchFillDimension.Statement)
    (hopen : NormalOpenMapping.Statement) (hreg : BranchInverseOffHypersurface.Statement)
    (hext : NormalRiemannExtension.Statement) (hirr : NormalLocallyIrreducible.Statement) :
    BranchInverseHolomorphic.Statement := by
  intro σ _ I h w k r φ B hI hIc hh hw hφd hφi hφZ hB hfill
  set Δ := Metric.ball (0 : Fin k → ℂ) r with hΔ
  have hk := hdim σ I h w k r φ B hI hh hw hφd hφi hφZ hB hfill
  set ψ : (σ → ℂ) → Fin k → ℂ := Function.invFunOn φ Δ with hψdef
  have hψφ : ∀ t ∈ Δ, ψ (φ t) = t := fun t ht => hφi.leftInvOn_invFunOn ht
  obtain ⟨O, hOo, hO⟩ := hopen σ I k Δ φ hI hIc hk Metric.isOpen_ball hφd hφi hφZ

  have hψc : ∀ z ∈ φ '' Δ, ContinuousWithinAt ψ (φ '' Δ) z := by
    rintro _ ⟨t, ht, rfl⟩
    rw [ContinuousWithinAt, hψφ t ht, tendsto_nhds]
    intro V hVo htV
    obtain ⟨O', hO'o, hO'⟩ := hopen σ I k (V ∩ Δ) φ hI hIc hk (hVo.inter Metric.isOpen_ball)
      (hφd.mono Set.inter_subset_right) (hφi.mono Set.inter_subset_right)
      (hφZ.mono_left Set.inter_subset_right)
    have hmem : φ t ∈ zeroSetIn I ∩ O' := hO' ▸ Set.mem_image_of_mem φ ⟨htV, ht⟩
    filter_upwards [inter_mem_nhdsWithin (φ '' Δ) (hO'o.mem_nhds hmem.2)] with z hz
    obtain ⟨⟨s, hs, rfl⟩, hzO'⟩ := hz
    have hs' : φ s ∈ φ '' (V ∩ Δ) := by rw [hO']; exact ⟨hφZ hs, hzO'⟩
    obtain ⟨s', hs'V, hss'⟩ := hs'
    rw [Set.mem_preimage, hψφ s hs, ← hφi hs'V.2 hs hss']
    exact hs'V.1
  obtain ⟨h', hh', hreg'⟩ := hreg σ I k hI hk
  have hψreg := hreg' Δ φ ψ Metric.isOpen_ball hφd hφi hφZ hψφ
  rw [hO] at hψreg hψc

  have hcoord : ∀ j : Fin k, ∃ g : (σ → ℂ) → ℂ, HolomorphicOnSubset g (zeroSetIn I ∩ O) ∧
      Set.EqOn g (fun z => ψ z j) ((zeroSetIn I ∩ O) \ {z | eval z h' = 0}) := by
    intro j
    refine hext σ I h' O (fun z => ψ z j) hI hIc hh' hOo ?_ ?_
    · intro z hz
      obtain ⟨U, hUo, hzU, F, hF, hFeq⟩ := hψreg z hz
      exact ⟨U, hUo, hzU, fun y => F y j, differentiableOn_pi.mp hF j,
        fun y hy => congrFun (hFeq hy) j⟩
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := r)).subset ?_
      rintro _ ⟨z, hz, rfl⟩
      have hz' : z ∈ φ '' Δ := by rw [hO]; exact hz.1
      obtain ⟨t, ht, rfl⟩ := hz'
      rw [Metric.mem_closedBall, dist_zero_right]
      show ‖ψ (φ t) j‖ ≤ r
      rw [hψφ t ht]
      exact (norm_le_pi_norm t j).trans (mem_ball_zero_iff.mp ht).le
  choose g hg hgeq using hcoord

  have hgψ : ∀ j, ∀ z ∈ zeroSetIn I ∩ O, g j z = ψ z j := by
    intro j z hz
    obtain ⟨B', -, hzB', hB'O, -, hdense⟩ := hirr σ I h' z hI hIc hh' hz.1 O (hOo.mem_nhds hz.2)
    set P := (zeroSetIn I ∩ B') \ {y | eval y h' = 0} with hP
    have hPsub : P ⊆ zeroSetIn I ∩ O := fun y hy => ⟨hy.1.1, hB'O hy.1.2⟩
    have : (𝓝[P] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hdense ⟨hz.1, hzB'⟩)
    have h1 : Tendsto (g j) (𝓝[P] z) (𝓝 (g j z)) := (((hg j).continuousWithinAt hz).mono hPsub).tendsto
    have h2 : Tendsto (fun y => ψ y j) (𝓝[P] z) (𝓝 (ψ z j)) :=
      (((continuous_apply j).continuousAt.comp_continuousWithinAt (hψc z hz)).mono hPsub).tendsto
    refine tendsto_nhds_unique h1 (h2.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hgeq j ⟨hPsub hy, hy.2⟩).symm
  refine ⟨ψ, ?_, hψφ⟩
  rw [hO]
  intro z hz
  choose U hUo hzU F hF hFeq using fun j => hg j z hz
  refine ⟨⋂ j, U j, isOpen_iInter_of_finite hUo, Set.mem_iInter.mpr hzU, fun y j => F j y,
    differentiableOn_pi.mpr fun j => (hF j).mono (Set.iInter_subset _ j), fun y hy => ?_⟩
  funext j
  show ψ y j = F j y
  rw [← hgψ j y hy.1]
  exact hFeq j ⟨hy.1, Set.mem_iInter.mp hy.2 j⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology IndefiniteRowSideFullHecke.ComplexSets

theorem NormalModelProjectionLocallyInjective.proof : NormalModelProjectionLocallyInjective.Statement := by
  intro n J M w hJ hdim hw
  choose a b hbJ hab using M.birational
  set B : MvPolynomial (Fin n) ℂ := ∏ i, b i with hB
  have hBJ : B ∉ J := fun h => by
    have := hJ
    obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact hbJ i hi

  set S : Set (Fin n → ℂ) := ComplexSets.zeroSet J ∩ ComplexSets.zeroSet (Ideal.span {B}) with hS
  have hSfin : S.Finite := CurveProperClosedFinite.proof n J _ hJ hdim
    (fun h => hBJ (h (Ideal.subset_span rfl)))

  choose P hPm hP using M.integral
  set F : Set (Fin n ⊕ Fin M.m → ℂ) := {z | z ∈ zeroSetIn M.ideal ∧ firstCoords z ∈ S} with hF
  have hFfin : F.Finite := by
    have hT : (⋃ x ∈ S, ({x} : Set (Fin n → ℂ)) ×ˢ
        Set.pi Set.univ (fun i => {y : ℂ | ((P i).map (eval x)).IsRoot y})).Finite :=
      hSfin.biUnion fun x _ => (Set.finite_singleton x).prod
        (Set.Finite.pi fun i => Polynomial.finite_setOfPred_isRoot ((hPm i).map (eval x)).ne_zero)
    refine (hT.image fun p => Sum.elim p.1 p.2).subset ?_
    intro z hz
    refine ⟨(firstCoords z, fun i => z (Sum.inr i)), ?_, ?_⟩
    · refine Set.mem_biUnion hz.2 ⟨rfl, fun i _ => ?_⟩
      exact isRoot_map_eval_of_mem_zeroSetIn hz.1 i (P i) (hP i)
    · funext s
      rcases s with j | i <;> rfl
  refine ⟨(F \ {w})ᶜ, (hFfin.subset Set.sdiff_subset).isClosed.isOpen_compl.mem_nhds
    (fun h => h.2 rfl), ?_⟩

  have hnear : ∀ z ∈ zeroSetIn M.ideal ∩ (F \ {w})ᶜ, (∃ i, eval (firstCoords z) (b i) = 0) → z = w := by
    rintro z ⟨hz, hzU⟩ ⟨i, hi⟩
    have hxJ : firstCoords z ∈ ComplexSets.zeroSet J := fun q hq => by
      rw [← M.comap_eq, Ideal.mem_comap] at hq
      have h := hz _ hq
      rw [eval_rename] at h
      exact h
    have hxB : firstCoords z ∈ ComplexSets.zeroSet (Ideal.span {B}) := fun q hq => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 hq
      rw [eval_mul, hB, map_prod, Finset.prod_eq_zero (Finset.mem_univ i) hi, zero_mul]
    by_contra hne
    exact hzU ⟨⟨hz, hxJ, hxB⟩, hne⟩
  intro z hz z' hz' hzz
  by_cases hbz : ∀ i, eval (firstCoords z) (b i) ≠ 0
  · have hbz' : ∀ i, eval (firstCoords z') (b i) ≠ 0 := hzz ▸ hbz
    rw [M.eq_graph_of_mem_zeroSetIn a b hab z hz.1 hbz, M.eq_graph_of_mem_zeroSetIn a b hab z' hz'.1 hbz', hzz]
  · simp only [not_forall, not_not] at hbz
    have hbz' : ∃ i, eval (firstCoords z') (b i) = 0 := hzz ▸ hbz
    rw [hnear z hz hbz, hnear z' hz' hbz']

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

noncomputable section

theorem FiniteProjectionsContainOpen.proof (h₁ : ConeAvoidsFinite.Statement)
    (h₂ : FiniteProjHomInjective.Statement) (h₃ : ConeAvoidsOpen.Statement)
    (h₄ : ConeAvoidsExists.Statement) : FiniteProjectionsContainOpen.Statement := by
  intro n d J hJ hd
  obtain ⟨A₀, N, hA₀⟩ := h₄ n d J hJ hd
  refine ⟨{A | ConeAvoids J A N}, h₃ n d N J, ⟨A₀, hA₀⟩, fun A hA => ?_⟩
  have hfin : (projHom J A).toRingHom.Finite := h₁ n d N J A hA
  exact ⟨h₂ n d J A hJ hd hfin, hfin⟩

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem CurveRegularOffFinite.proof (hG : FrameGraphGeneric.Statement)
    (hP : CurveProperClosedFinite.Statement) : CurveRegularOffFinite.Statement := by
  intro n W hW hdim
  have hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = ((1 : ℕ) : WithBot ℕ∞) := by
    rw [hdim]; rfl
  let b := EuclideanSpace.basisFun (Fin n) ℂ
  obtain ⟨I₀, q, hcard, hqW, hreg⟩ := hG n 1 W hW hd b
  obtain ⟨i₀, hI₀⟩ := Finset.card_eq_one.mp hcard
  have hi₀ : i₀ ∈ I₀ := by rw [hI₀]; exact Finset.mem_singleton_self i₀
  have hsub : ∀ j : I₀, j = ⟨i₀, hi₀⟩ := fun j => Subtype.ext (Finset.mem_singleton.mp (hI₀ ▸ j.2))
  have hKW : ¬ Ideal.span {q} ≤ W := fun h => hqW (h (Ideal.subset_span rfl))
  refine ⟨zeroSet W ∩ zeroSet (Ideal.span {q}), hP n W _ hW hdim hKW, ?_⟩
  intro x hx hxF
  have hqx : eval x q ≠ 0 := by
    intro h0
    refine hxF ⟨hx, fun p hp => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    simp [h0]

  let T : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    ((EuclideanSpace.equiv (Fin n) ℂ).symm : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n))
  let S : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ) :=
    ((EuclideanSpace.equiv (Fin n) ℂ) : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ))
  have hST : ∀ y, S (T y) = y := fun y => rfl
  have hTS : ∀ w, T (S w) = w := fun w => rfl
  have hZ : ∀ y : Fin n → ℂ, y ∈ zeroSet W ↔ T y ∈ zeroSetEuc W := fun y => Iff.rfl
  obtain ⟨Ω, V, g, hΩ, hV, hxV, hg, hproj, hgraph⟩ := hreg (T x) ((hZ x).mp hx) hqx

  let ι : ℂ →L[ℂ] (I₀ → ℂ) := ContinuousLinearMap.pi fun _ : I₀ => ContinuousLinearMap.id ℂ ℂ
  let A : (Fin n → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i₀
  have hO : IsOpen (ι ⁻¹' Ω) := hΩ.preimage ι.continuous
  refine ⟨A, ι ⁻¹' Ω, T ⁻¹' V, fun y => S (g (ι y)), hO, hV.preimage T.continuous, hxV, ?_, ?_, ?_⟩
  · exact (S.differentiable.comp_differentiableOn
      (hg.comp ι.differentiable.differentiableOn fun y hy => hy)).analyticOnNhd hO
  · intro y hy
    have h1 := congrFun (hproj (ι y) hy) ⟨i₀, hi₀⟩
    simp only [frameProj, b, EuclideanSpace.basisFun_inner] at h1
    exact h1
  · ext x'
    constructor
    · rintro ⟨hx'Z, hx'V⟩
      have hmem : T x' ∈ zeroSetEuc W ∩ V := ⟨(hZ x').mp hx'Z, hx'V⟩
      rw [hgraph] at hmem
      obtain ⟨u, hu, hgu⟩ := hmem
      have hιu : ι (u ⟨i₀, hi₀⟩) = u := funext fun j => by rw [hsub j]; rfl
      refine ⟨u ⟨i₀, hi₀⟩, ?_, ?_⟩
      · show ι _ ∈ Ω
        rwa [hιu]
      · simp only [hιu, hgu, hST]
    · rintro ⟨y, hy, rfl⟩
      have hmem : g (ι y) ∈ zeroSetEuc W ∩ V := hgraph ▸ Set.mem_image_of_mem g hy
      exact ⟨(hZ _).mpr (by rw [hTS]; exact hmem.1), by show T (S (g (ι y))) ∈ V; rw [hTS]; exact hmem.2⟩

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm
open scoped ContDiff

noncomputable section

namespace FormIntegralPositivity

variable {n : ℕ}

theorem analyticAt_sheet {d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s) :
    AnalyticAt ℂ s (A *ᵥ x) := by
  obtain ⟨U, hU, hxU, hsU, -⟩ := hs
  rw [analyticAt_pi_iff]
  intro i
  exact ReciprocityTheory.ChartRestriction.G.Geo.osgood d U (fun y => s y i) hU
    (fun y hy => differentiableWithinAt_pi.mp (hsU y hy) i) (A *ᵥ x) hxU

end FormIntegralPositivity


end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem VarSlabMeasure.proof (hV : VarietySlabMeasure.Statement) : VarSlabMeasure.Statement := by
  intro n d J u R hJ hd hu
  obtain ⟨C, α, -, hα, hb⟩ := hV n d J u hJ hd.le hu R
  refine ⟨C, α, hα, fun ε hε hε1 => ?_⟩
  have hset : zeroSetEuc J ∩ {z | ‖z‖ ≤ R} ∩ {z | ‖∑ j, u j * z j‖ ≤ ε} =
      {z | z ∈ zeroSetEuc J ∧ ‖z‖ ≤ R ∧ ‖∑ j, u j * z j‖ ≤ ε} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_assoc]
  rw [hset]
  exact hb ε hε hε1

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

def PolyGermPointPow.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (q : MvPolynomial σ ℂ),
    polyGerm w q ∈ holGermPointIdeal w ^ k → q ∈ RingHom.ker (MvPolynomial.eval w) ^ k

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
