module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle016
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter Set

theorem IrreducibleFiniteGermProjectionOpenAt.proof
    (hpts : IrreducibleGermPointsOffDiscriminant.Statement) :
    IrreducibleFiniteGermProjectionOpenAt.Statement := by
  intro σ _ X x d A hX hirr hiso hinj V hV
  obtain ⟨δ, hδa, hδne, hδpts⟩ := hpts σ X x d A hX hirr hiso hinj
  obtain ⟨N, k, f, hNo, hxN, hf, hXN⟩ := hX
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hV (hNo.mem_nhds hxN))
  set r' := r / 2 with hr'
  have hr'0 : 0 < r' := by positivity
  have hcb : closedBall x r' ⊆ V ∩ N := (closedBall_subset_ball (by linarith)).trans hrV

  set K : Set (σ → ℂ) := closedBall x r' ∩ ⋂ i, (closedBall x r' ∩ f i ⁻¹' {0}) with hK
  have hKc : IsCompact K := by
    refine (isCompact_closedBall x r').of_isClosed_subset ?_ inter_subset_left
    refine isClosed_closedBall.inter (isClosed_iInter fun i => ?_)
    exact ((hf i).continuousOn.mono (hcb.trans inter_subset_right)).preimage_isClosed_of_isClosed
      isClosed_closedBall isClosed_singleton
  have hKV : A '' K ⊆ A '' (X ∩ V) := by
    refine image_mono fun z hz => ?_
    have hzN : z ∈ N := (hcb hz.1).2
    have hzX : z ∈ X ∩ N := by
      rw [hXN]
      exact ⟨hzN, fun i => by simpa using ((mem_iInter.mp hz.2) i).2⟩
    exact ⟨hzX.1, (hcb hz.1).1⟩
  have hball : ∀ z ∈ X ∩ ball x r', z ∈ K := by
    intro z hz
    have hzcb : z ∈ closedBall x r' := ball_subset_closedBall hz.2
    have hzN : z ∈ X ∩ N := ⟨hz.1, (hcb hzcb).2⟩
    rw [hXN] at hzN
    exact ⟨hzcb, mem_iInter.mpr fun i => ⟨hzcb, by simpa using hzN.2 i⟩⟩

  obtain ⟨ε₁, hε₁, hε₁a⟩ := hδa.exists_ball_analyticOnNhd
  obtain ⟨ε₂, hε₂, hε₂p⟩ := Metric.eventually_nhds_iff.mp (hδpts (ball x r') (ball_mem_nhds x hr'0))
  set ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  have hDa : AnalyticOnNhd ℂ δ (ball (A x) ε) := hε₁a.mono (ball_subset_ball (min_le_left _ _))
  have hsub : {y | y ∈ ball (A x) ε ∧ δ y ≠ 0} ⊆ A '' K := by
    rintro y ⟨hy, hδy⟩
    have hy2 : dist y (A x) < ε₂ := lt_of_lt_of_le (mem_ball.mp hy) (min_le_right _ _)
    obtain ⟨x', hx', rfl⟩ := hε₂p hy2 hδy
    exact ⟨x', hball x' hx', rfl⟩
  have hD : ball (A x) ε ⊆ A '' K := by
    intro y hy
    refine (hKc.image A.continuous).isClosed.closure_subset_iff.mpr hsub (mem_closure_iff_frequently.mpr ?_)
    intro hev
    have hev' : δ =ᶠ[𝓝 y] 0 := by
      filter_upwards [hev, isOpen_ball.mem_nhds hy] with z hz hzD
      by_contra hz0
      exact hz ⟨hzD, hz0⟩
    have hzero := hDa.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball (A x) ε).isPreconnected hy hev'
    apply hδne
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε)] with z hz using hzero hz
  exact Filter.mem_of_superset (ball_mem_nhds (A x) hε) (hD.trans hKV)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem eventually_eq_zero_of_lines {d : ℕ} {h : (Fin d → ℂ) → ℂ} {a : Fin d → ℂ}
    (ha : AnalyticAt ℂ h a) (hl : ∀ v : Fin d → ℂ, ∀ᶠ t in 𝓝 (0 : ℂ), h (a + t • v) = 0) :
    ∀ᶠ y in 𝓝 a, h y = 0 := by
  obtain ⟨r, hr, han⟩ := ha.exists_ball_analyticOnNhd
  filter_upwards [Metric.ball_mem_nhds a hr] with y hy
  by_cases hv : y - a = 0
  · have hya : y = a := sub_eq_zero.1 hv
    have h0 := (hl 0).self_of_nhds
    simpa [hya] using h0
  have hvpos : 0 < ‖y - a‖ := norm_pos_iff.2 hv
  have hmaps : ∀ t ∈ Metric.ball (0 : ℂ) (r / ‖y - a‖), a + t • (y - a) ∈ Metric.ball a r := by
    intro t ht
    rw [Metric.mem_ball, dist_zero_right, lt_div_iff₀ hvpos] at ht
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    exact ht
  have hg : AnalyticOnNhd ℂ (fun t : ℂ => h (a + t • (y - a))) (Metric.ball (0 : ℂ) (r / ‖y - a‖)) := by
    intro t ht
    have h1 : AnalyticAt ℂ (fun t : ℂ => a + t • (y - a)) t := by fun_prop
    exact AnalyticAt.comp (g := h) (f := fun s : ℂ => a + s • (y - a)) (han _ (hmaps t ht)) h1
  have h1 : (1 : ℂ) ∈ Metric.ball (0 : ℂ) (r / ‖y - a‖) := by
    rw [Metric.mem_ball, dist_zero_right, norm_one, one_lt_div hvpos, ← dist_eq_norm]
    exact hy
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) (r / ‖y - a‖) := Metric.mem_ball_self (div_pos hr hvpos)
  have hz := hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball (0 : ℂ) _).isPreconnected h0
    (by filter_upwards [hl (y - a)] with t ht using ht) h1
  simpa using hz

theorem exists_line_eventually_ne_zero {d : ℕ} {h : (Fin d → ℂ) → ℂ} {a : Fin d → ℂ}
    (ha : AnalyticAt ℂ h a) (hne : ¬ ∀ᶠ y in 𝓝 a, h y = 0) :
    ∃ v : Fin d → ℂ, ∀ᶠ t in 𝓝[≠] (0 : ℂ), h (a + t • v) ≠ 0 := by
  by_contra hcon
  refine hne (eventually_eq_zero_of_lines ha fun v => ?_)
  have h1 : AnalyticAt ℂ (fun t : ℂ => a + t • v) 0 := by fun_prop
  have ha' : AnalyticAt ℂ h (a + (0 : ℂ) • v) := by simpa using ha
  rcases (AnalyticAt.comp (g := h) (f := fun s : ℂ => a + s • v) ha' h1).eventually_eq_zero_or_eventually_ne_zero with h0 | h0
  · exact h0
  · exact absurd ⟨v, h0⟩ hcon

theorem exists_proj_fibres_line {d : ℕ} (v : Fin d → ℂ) (hv : v ≠ 0) :
    ∃ π : (Fin d → ℂ) →L[ℂ] (Fin (d - 1) → ℂ), ∀ y y', π y = π y' → ∃ t : ℂ, y = y' + t • v := by
  have hrank : Module.finrank ℂ ((Fin d → ℂ) ⧸ (ℂ ∙ v)) = Module.finrank ℂ (Fin (d - 1) → ℂ) := by
    have h1 := Submodule.finrank_quotient_add_finrank (ℂ ∙ v)
    rw [finrank_span_singleton hv, Module.finrank_fin_fun] at h1
    rw [Module.finrank_fin_fun]
    omega
  let e := LinearEquiv.ofFinrankEq _ _ hrank
  refine ⟨LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ (ℂ ∙ v).mkQ), fun y y' hyy => ?_⟩
  have hq : (ℂ ∙ v).mkQ y = (ℂ ∙ v).mkQ y' := e.injective hyy
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_span_singleton] at hq
  obtain ⟨t, ht⟩ := hq
  exact ⟨t, by rw [ht]; abel⟩

theorem GermFiniteProjection.proof : GermFiniteProjection.Statement := by
  intro σ _ X w _ hirr
  classical
  have hw : w ∈ X := hirr.1
  have hP : ∃ d : ℕ, ∃ A : (σ → ℂ) →L[ℂ] (Fin d → ℂ), ∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w := by
    let e : (σ → ℂ) ≃ₗ[ℂ] (Fin (Fintype.card σ) → ℂ) :=
      LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin σ).symm
    exact ⟨Fintype.card σ, LinearMap.toContinuousLinearMap e.toLinearMap, Set.univ, univ_mem,
      fun x _ hx => e.injective hx⟩
  obtain ⟨A, W, hW, hAW⟩ := Nat.find_spec hP
  refine ⟨Nat.find hP, A, ⟨W, hW, hAW⟩, fun h hh hXh => ?_⟩
  by_contra hne
  have hAw : h (A w) = 0 := hXh.self_of_nhds hw
  obtain ⟨v, hv⟩ := exists_line_eventually_ne_zero hh hne
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨t, ht⟩ := hv.exists
    simp [hAw] at ht
  have hd : Nat.find hP - 1 < Nat.find hP := by
    have : 0 < Nat.find hP := Nat.pos_of_ne_zero fun h0 => hv0 (funext fun i => (Fin.cast h0 i).elim0)
    omega
  obtain ⟨π, hπ⟩ := exists_proj_fibres_line v hv0
  obtain ⟨ε, hε, hεv⟩ := Metric.mem_nhdsWithin_iff.1 hv
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have hcont : ∀ᶠ x in 𝓝 w, A x ∈ Metric.ball (A w) (ε * ‖v‖) :=
    A.continuous.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (mul_pos hε hvpos))
  refine Nat.find_min hP hd ⟨π.comp A, W ∩ {x | (x ∈ X → h (A x) = 0) ∧ A x ∈ Metric.ball (A w) (ε * ‖v‖)},
    inter_mem hW (hXh.and hcont), ?_⟩
  rintro x ⟨hxX, hxW, hxh, hxb⟩ hπx
  apply hAW x ⟨hxX, hxW⟩
  obtain ⟨t, ht⟩ := hπ (A x) (A w) hπx
  by_cases ht0 : t = 0
  · simpa [ht0] using ht
  exfalso
  have htε : t ∈ Metric.ball (0 : ℂ) ε := by
    rw [Metric.mem_ball, dist_zero_right]
    have hb : ‖t • v‖ < ε * ‖v‖ := by
      rw [Metric.mem_ball, dist_eq_norm, ht, add_sub_cancel_left] at hxb
      exact hxb
    rw [norm_smul] at hb
    exact lt_of_mul_lt_mul_right hb hvpos.le
  exact hεv ⟨htε, ht0⟩ (by rw [← ht]; exact hxh hxX)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter

theorem IsolatedFibreNear.proof (hFin : CompactHolomorphicFibreFinite.Statement) :
    IsolatedFibreNear.Statement := by
  intro σ _ X w d A hX hiso
  obtain ⟨N, k, f, hN, hwN, hf, hXN⟩ := hX
  obtain ⟨W, hW, hWiso⟩ := hiso
  have memX : ∀ z, z ∈ N → (∀ i, f i z = 0) → z ∈ X := fun z hz h0 => by
    have : z ∈ X ∩ N := by rw [hXN]; exact ⟨hz, h0⟩
    exact this.1
  have zerosX : ∀ z, z ∈ X → z ∈ N → ∀ i, f i z = 0 := fun z hzX hzN => by
    have : z ∈ X ∩ N := ⟨hzX, hzN⟩
    rw [hXN] at this
    exact this.2
  obtain ⟨r, hr, hrsub⟩ := (nhds_basis_closedBall (x := w)).mem_iff.1 (inter_mem (hN.mem_nhds hwN) hW)
  have hBN : closedBall w r ⊆ N := fun z hz => (hrsub hz).1
  have hBW : closedBall w r ⊆ W := fun z hz => (hrsub hz).2

  set g : (σ → ℂ) → (Fin k → ℂ) := fun z i => f i z with hg
  have hgc : ContinuousOn g (closedBall w r) :=
    continuousOn_pi.2 fun i => ((hf i).continuousOn).mono hBN
  set K := sphere w r ∩ g ⁻¹' {0} with hK
  have hKc : IsCompact K := by
    refine (isCompact_sphere w r).of_isClosed_subset ?_ Set.inter_subset_left
    exact (hgc.mono sphere_subset_closedBall).preimage_isClosed_of_isClosed isClosed_sphere isClosed_singleton
  have hAK : A w ∉ A '' K := by
    rintro ⟨z, ⟨hzs, hz0⟩, hzA⟩
    have hzB : z ∈ closedBall w r := sphere_subset_closedBall hzs
    have hz0' : ∀ i, f i z = 0 := fun i => congrFun hz0 i
    have hzw : z = w := hWiso z ⟨memX z (hBN hzB) hz0', hBW hzB⟩ hzA
    rw [mem_sphere, hzw, dist_self] at hzs
    exact hr.ne hzs
  obtain ⟨ε, hε, hεsub⟩ :=
    Metric.isOpen_iff.1 ((hKc.image A.continuous).isClosed.isOpen_compl) (A w) hAK
  refine ⟨ball w r ∩ A ⁻¹' ball (A w) ε, ?_, ?_⟩
  · exact inter_mem (ball_mem_nhds w hr) (A.continuous.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hε))
  rintro x ⟨hxX, hxB, hxD⟩

  set F := {z | z ∈ ball w r ∧ (∀ i, f i z = 0) ∧ A z = A x} with hF
  have hFeq : F = closedBall w r ∩ (fun z => (g z, A z)) ⁻¹' {(0, A x)} := by
    ext z
    simp only [hF, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Prod.mk.injEq, hg, funext_iff, Pi.zero_apply]
    constructor
    · rintro ⟨hzb, h0, hzA⟩
      exact ⟨ball_subset_closedBall hzb, h0, hzA⟩
    · rintro ⟨hzb, h0, hzA⟩
      refine ⟨?_, h0, hzA⟩
      rcases (mem_closedBall.1 hzb).lt_or_eq with hlt | heq
      · exact mem_ball.2 hlt
      · exfalso
        have hzK : z ∈ K := ⟨mem_sphere.2 heq, by funext i; exact h0 i⟩
        apply hεsub (show A z ∈ ball (A w) ε by rw [funext hzA]; exact hxD)
        exact ⟨z, hzK, rfl⟩
  have hFc : IsCompact F := by
    rw [hFeq]
    refine (isCompact_closedBall w r).of_isClosed_subset ?_ Set.inter_subset_left
    exact (hgc.prodMk A.continuous.continuousOn).preimage_isClosed_of_isClosed isClosed_closedBall
      isClosed_singleton

  set n := Fintype.card σ
  let L : (σ → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : Fin n => ℂ) (Fintype.equivFin σ)
  set U : Set (Fin n → ℂ) := L.symm ⁻¹' ball w r with hU
  set h : (Fin n → ℂ) → Fin (k + d) → ℂ :=
    fun v => Fin.append (fun i => f i (L.symm v)) (A (L.symm v)) with hh
  set y : Fin (k + d) → ℂ := Fin.append (0 : Fin k → ℂ) (A x) with hy
  have hUo : IsOpen U := isOpen_ball.preimage L.symm.continuous
  have hhd : DifferentiableOn ℂ h U := by
    refine differentiableOn_pi.2 fun j => ?_
    refine Fin.addCases (fun i => ?_) (fun j => ?_) j
    · simp only [hh, Fin.append_left]
      exact ((hf i).differentiableOn.mono (ball_subset_closedBall.trans hBN)).comp
        L.symm.differentiable.differentiableOn (fun v hv => hv)
    · simp only [hh, Fin.append_right]
      exact ((differentiable_apply (𝕜 := ℂ) j).comp
        (A.differentiable.comp L.symm.differentiable)).differentiableOn
  have hfib : {v | v ∈ U ∧ h v = y} = L.symm ⁻¹' F := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hU, hF, hh, hy]
    constructor
    · rintro ⟨hv, he⟩
      refine ⟨hv, fun i => ?_, ?_⟩
      · simpa using congrFun he (Fin.castAdd d i)
      · funext j
        simpa using congrFun he (Fin.natAdd k j)
    · rintro ⟨hv, h0, hA⟩
      refine ⟨hv, funext fun j => ?_⟩
      refine Fin.addCases (fun i => ?_) (fun j => ?_) j
      · simp [h0 i]
      · simp [hA]
  have hfibc : IsCompact {v | v ∈ U ∧ h v = y} := by
    rw [hfib, ← L.image_eq_preimage_symm]
    exact hFc.image L.continuous
  have hFfin : F.Finite := by
    have h1 := (hFin n (k + d) U h y hUo hhd hfibc).image L.symm
    rwa [hfib, Set.image_preimage_eq _ L.symm.surjective] at h1

  refine ⟨ball w r \ (F \ {x}), ?_, ?_⟩
  · exact (isOpen_ball.sdiff (hFfin.sdiff).isClosed).mem_nhds ⟨hxB, fun hx => hx.2 rfl⟩
  rintro x' ⟨hx'X, hx'B, hx'F⟩ hx'A
  by_contra hne
  exact hx'F ⟨⟨hx'B, zerosX x' hx'X (hBN (ball_subset_closedBall hx'B)), hx'A⟩, hne⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem exists_proper_projection_nbhd {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {w : σ → ℂ} {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (hX : IsAnalyticNear X w) (hw : w ∈ X)
    (hiso : ∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) {U : Set (σ → ℂ)} (hU : U ∈ 𝓝 w) :
    ∃ (B : Set (σ → ℂ)) (D : Set (Fin d → ℂ)), IsOpen B ∧ B ⊆ U ∧ w ∈ X ∩ B ∧ IsOpen D ∧
      IsPreconnected D ∧ Set.MapsTo A (X ∩ B) D ∧
      (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ X ∩ B ∧ A x ∈ K}) ∧
      (∀ x ∈ X ∩ B, A x = A w → x = w) := by
  obtain ⟨N, k, f, hNo, hwN, hf, hXN⟩ := hX
  obtain ⟨W, hW, hisoW⟩ := hiso
  obtain ⟨r₀, hr₀, hball⟩ :=
    Metric.mem_nhds_iff.1 (Filter.inter_mem (Filter.inter_mem hU (hNo.mem_nhds hwN)) hW)
  set r := r₀ / 2 with hr
  have hr0 : 0 < r := half_pos hr₀
  have hcb : Metric.closedBall w r ⊆ U ∩ N ∩ W :=
    (Metric.closedBall_subset_ball (half_lt_self hr₀)).trans hball

  set Z : Set (σ → ℂ) := Metric.closedBall w r ∩ ⋂ i, (Metric.closedBall w r ∩ f i ⁻¹' {0}) with hZ
  have hZc : IsClosed Z := by
    refine Metric.isClosed_closedBall.inter (isClosed_iInter fun i => ?_)
    exact ((hf i).continuousOn.mono fun z hz => (hcb hz).1.2).preimage_isClosed_of_isClosed
      Metric.isClosed_closedBall isClosed_singleton
  have hZk : IsCompact Z := (isCompact_closedBall w r).of_isClosed_subset hZc Set.inter_subset_left
  have hZX : ∀ z ∈ Metric.closedBall w r, (z ∈ X ↔ z ∈ Z) := by
    intro z hz
    have hzN : z ∈ N := (hcb hz).1.2
    constructor
    · intro hzX
      have h1 : z ∈ X ∩ N := ⟨hzX, hzN⟩
      rw [hXN] at h1
      exact ⟨hz, Set.mem_iInter.2 fun i => ⟨hz, h1.2 i⟩⟩
    · intro hzZ
      have h2 : z ∈ {z | z ∈ N ∧ ∀ i, f i z = 0} := ⟨hzN, fun i => (Set.mem_iInter.1 hzZ.2 i).2⟩
      rw [← hXN] at h2
      exact h2.1

  have hSk : IsCompact (Z ∩ Metric.sphere w r) := hZk.inter_right Metric.isClosed_sphere
  have hAS : A w ∉ A '' (Z ∩ Metric.sphere w r) := by
    rintro ⟨x, ⟨hxZ, hxs⟩, hxA⟩
    have hxcb : x ∈ Metric.closedBall w r := Metric.sphere_subset_closedBall hxs
    have hxw := hisoW x ⟨(hZX x hxcb).2 hxZ, (hcb hxcb).2⟩ hxA
    rw [hxw, Metric.mem_sphere, dist_self] at hxs
    exact hr0.ne hxs
  obtain ⟨ε, hε, hεS⟩ :=
    Metric.mem_nhds_iff.1 ((hSk.image A.continuous).isClosed.isOpen_compl.mem_nhds hAS)
  refine ⟨Metric.ball w r ∩ A ⁻¹' Metric.ball (A w) ε, Metric.ball (A w) ε,
    Metric.isOpen_ball.inter (Metric.isOpen_ball.preimage A.continuous), ?_,
    ⟨hw, Metric.mem_ball_self hr0, Set.mem_preimage.mpr (Metric.mem_ball_self hε)⟩, Metric.isOpen_ball,
    (convex_ball _ _).isPreconnected, fun x hx => hx.2.2, ?_, ?_⟩
  · exact fun x hx => (hcb (Metric.ball_subset_closedBall hx.1)).1.1
  · intro K hKD hK
    have heq : {x | x ∈ X ∩ (Metric.ball w r ∩ A ⁻¹' Metric.ball (A w) ε) ∧ A x ∈ K} =
        Z ∩ A ⁻¹' K := by
      ext x
      constructor
      · rintro ⟨⟨hxX, hxb, -⟩, hxK⟩
        exact ⟨(hZX x (Metric.ball_subset_closedBall hxb)).1 hxX, hxK⟩
      · rintro ⟨hxZ, hxK⟩
        have hxcb : x ∈ Metric.closedBall w r := hxZ.1
        refine ⟨⟨(hZX x hxcb).2 hxZ, ?_, hKD hxK⟩, hxK⟩
        by_contra hxb
        have hxs : x ∈ Metric.sphere w r :=
          Metric.mem_sphere.2 (le_antisymm (Metric.mem_closedBall.1 hxcb)
            (not_lt.1 fun h => hxb (Metric.mem_ball.2 h)))
        exact hεS (hKD hxK) ⟨x, ⟨hxZ, hxs⟩, rfl⟩
    rw [heq]
    exact hZk.inter_right (hK.isClosed.preimage A.continuous)
  · exact fun x hx hxA => hisoW x ⟨hx.1, (hcb (Metric.ball_subset_closedBall hx.2.1)).2⟩ hxA

theorem LocalParametrisation.proof (hproj : GermFiniteProjection.Statement)
    (hcov : FiniteGermProjectionCover.Statement) : LocalParametrisation.Statement := by
  intro σ _ X w hX hirr U hU
  obtain ⟨d, A, hiso, hinj⟩ := hproj σ X w hX hirr
  obtain ⟨N₀, hN₀, hcovB⟩ := hcov σ X w d A hX hirr hiso hinj
  obtain ⟨B, D, hBo, hBU, hwB, hDo, hDc, hmaps, hprop, hisoB⟩ :=
    exists_proper_projection_nbhd A hX hirr.1 hiso (Filter.inter_mem hU hN₀)
  obtain ⟨δ, N, hP⟩ :=
    hcovB B D hBo (hBU.trans Set.inter_subset_right) hwB hDo hDc hmaps hprop hisoB
  exact ⟨d, A, B, D, δ, N, hBU.trans Set.inter_subset_left, hP⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem IrreducibleGermProjectionOpenNear.proof (hiso : IsolatedFibreNear.Statement)
    (himg : IrreducibleGermProjectionImageNear.Statement) (hopen : FiniteGermProjectionOpenAt.Statement) :
    IrreducibleGermProjectionOpenNear.Statement := by
  intro σ _ X w d A hX hirr hisow hinj
  obtain ⟨N₁, hN₁, h₁⟩ := hiso σ X w d A hX hisow
  obtain ⟨N₂, hN₂, h₂⟩ := himg σ X w d A hX hirr hisow hinj
  obtain ⟨N, k, f, hNo, hwN, hf, hXN⟩ := hX
  refine ⟨N₁ ∩ N₂ ∩ N, Filter.inter_mem (Filter.inter_mem hN₁ hN₂) (hNo.mem_nhds hwN), ?_⟩
  rintro x ⟨hxX, ⟨hx₁, hx₂⟩, hxN⟩ V hV

  have hXx : IsAnalyticNear X x := ⟨N, k, f, hNo, hxN, hf, hXN⟩
  exact hopen σ X x d A hXx (h₁ x ⟨hxX, hx₁⟩) (h₂ x ⟨hxX, hx₂⟩) V hV

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem IrreducibleGermRegularConnected.proof (hpar : LocalParametrisation.Statement)
    (hsheets : ParametrisationSheetsConnected.Statement) :
    IrreducibleGermRegularConnected.Statement := by
  intro σ _ X w hX hirr U hU
  obtain ⟨d, A, B, D, δ, N, hBU, hP⟩ := hpar σ X w hX hirr U hU
  have hS := hsheets σ X w B d A D δ N hP hirr
  obtain ⟨hBo, hwXB, -, -, -, -, -, -, -, -, hchart, hdense⟩ := hP

  have hSreg : {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ⊆ regLocus (X ∩ B) := by
    rintro x ⟨hxXB, hx⟩
    obtain ⟨O, V, g, hO, hV, hxV, hg, hAg, hXV⟩ := hchart x hxXB hx
    exact ⟨hxXB, d, A, O, V, g, hO, hV, hxV, hg, hAg, hXV⟩
  exact ⟨B, hBo, hwXB.2, hBU, hS.subset_closure hSreg ((regLocus_subset _).trans hdense)⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
