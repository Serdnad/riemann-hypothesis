module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle017
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
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem IrreducibleGermComplementConnected.proof (hdense : RegularLocusDense.Statement)
    (hconn : IrreducibleGermRegularConnected.Statement)
    (hzeros : ManifoldZerosComplementConnected.Statement) :
    IrreducibleGermComplementConnected.Statement := by
  intro σ _ X w h hX hirr hh hnot U hU
  obtain ⟨N, hNo, hwN, hN⟩ := hdense σ X w hX
  have hU' : U ∩ N ∩ {z | AnalyticAt ℂ h z} ∈ 𝓝 w :=
    inter_mem (inter_mem hU (hNo.mem_nhds hwN)) hh.eventually_analyticAt
  obtain ⟨B, hBo, hwB, hBU, hR⟩ := hconn σ X w hX hirr _ hU'
  have hBh : ∀ z ∈ B, AnalyticAt ℂ h z := fun z hz => (hBU hz).2
  have hcl : X ∩ B ⊆ closure (regLocus (X ∩ B)) := hN B hBo fun z hz => (hBU hz).1.2

  have hcl' : (X ∩ B) \ {z | h z = 0} ⊆ closure (regLocus (X ∩ B) \ {z | h z = 0}) := by
    rintro z ⟨hzXB, hz0⟩
    rw [mem_closure_iff_nhds]
    intro t ht
    have hne : {y | h y ≠ 0} ∈ 𝓝 z := (hBh z hzXB.2).continuousAt.eventually_ne hz0
    obtain ⟨y, ⟨hyt, hyh⟩, hyR⟩ := mem_closure_iff_nhds.1 (hcl hzXB) _ (inter_mem ht hne)
    exact ⟨y, hyt, hyR, hyh⟩

  have hex : ∃ x ∈ regLocus (X ∩ B), h x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hnot
    filter_upwards [hBo.mem_nhds hwB] with z hzB hzX
    by_contra hz0
    obtain ⟨y, hyR, hyh⟩ := closure_nonempty_iff.1 ⟨z, hcl' ⟨⟨hzX, hzB⟩, hz0⟩⟩
    exact hyh (hcon y hyR)
  have hRc : IsPreconnected (regLocus (X ∩ B) \ {z | h z = 0}) :=
    hzeros σ _ h hR (fun x hx => isRegularPointOf_regLocus hx)
      (fun x hx => hBh x (regLocus_subset _ hx).2) hex
  exact ⟨B, hBo, hwB, fun z hz => (hBU hz).1.1,
    hRc.subset_closure (Set.sdiff_subset_sdiff_left (regLocus_subset _)) hcl'⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric Set

theorem le_of_isolated_fibres (hfi : HolomorphicFibreInfinite.Statement) {e d : ℕ} {O : Set (Fin e → ℂ)}
    {φ : (Fin e → ℂ) → Fin d → ℂ} (hO : IsOpen O) (hne : O.Nonempty) (hφ : DifferentiableOn ℂ φ O)
    (hiso : ∀ t ∈ O, ∃ W ∈ 𝓝 t, ∀ v ∈ W, v ∈ O → φ v = φ t → v = t) : e ≤ d := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨y0, hy0⟩ := hne
  obtain ⟨ρ, hρ, hρO⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hO.mem_nhds hy0)
  obtain ⟨y, hy⟩ := hfi e d (ball y0 ρ) φ hlt isOpen_ball ⟨y0, mem_ball_self hρ⟩
    (hφ.mono (ball_subset_closedBall.trans hρO))
  obtain ⟨p, hpK, hpacc⟩ := hy.exists_accPt_of_subset_isCompact (isCompact_closedBall y0 ρ)
    (fun t ht => ball_subset_closedBall ht.1)
  have hpO : p ∈ O := hρO hpK
  have hcl : p ∈ closure {t | t ∈ ball y0 ρ ∧ φ t = y} := mem_closure_iff_nhds.2 fun U hU => by
    obtain ⟨q, hq, -⟩ := accPt_iff_nhds.1 hpacc U hU
    exact ⟨q, hq⟩
  have hφp : φ p = y := by
    have h1 := mem_closure_image ((hφ p hpO).differentiableAt (hO.mem_nhds hpO)).continuousAt hcl
    have h2 : φ '' {t | t ∈ ball y0 ρ ∧ φ t = y} ⊆ {y} := by
      rintro _ ⟨t, ht, rfl⟩
      exact ht.2
    simpa using closure_mono h2 h1
  obtain ⟨W, hW, hWiso⟩ := hiso p hpO
  obtain ⟨q, ⟨hqW, hqB, hqy⟩, hqp⟩ := accPt_iff_nhds.1 hpacc W hW
  exact hqp (hWiso q hqW (hρO (ball_subset_closedBall hqB)) (hqy.trans hφp.symm))

theorem IrreducibleGermProjectionImageNear.proof (hdim : IrreducibleGermRegularDimGe.Statement)
    (hisoN : IsolatedFibreNear.Statement) (hreg : RegularLocusDense.Statement)
    (hopen : HolomorphicIsolatedFibreOpen.Statement) (hfi : HolomorphicFibreInfinite.Statement) :
    IrreducibleGermProjectionImageNear.Statement := by
  intro σ _ X w d A hX hirr hfin hnd
  obtain ⟨N1, hN1, hdimN⟩ := hdim σ X w d A hX hirr hfin hnd
  obtain ⟨N2, hN2, hisoX⟩ := hisoN σ X w d A hX hfin
  obtain ⟨N3, hN3o, hwN3, hdense⟩ := hreg σ X w hX
  refine ⟨interior (N1 ∩ N2) ∩ N3,
    inter_mem (interior_mem_nhds.2 (inter_mem hN1 hN2)) (hN3o.mem_nhds hwN3), ?_⟩
  have hBo : IsOpen (interior (N1 ∩ N2) ∩ N3) := isOpen_interior.inter hN3o
  rintro x ⟨hxX, hxB⟩ h hh hvan
  obtain ⟨ε, hε, hhb⟩ := hh.exists_ball_analyticOnNhd
  obtain ⟨V, hV, hVo, hxV⟩ := _root_.mem_nhds_iff.1 hvan
  set V1 := V ∩ (interior (N1 ∩ N2) ∩ N3) ∩ A ⁻¹' ball (A x) ε with hV1
  have hV1o : IsOpen V1 := (hVo.inter hBo).inter (isOpen_ball.preimage A.continuous)
  have hxV1 : x ∈ V1 := ⟨⟨hxV, hxB⟩, by exact Set.mem_preimage.mpr (mem_ball_self hε)⟩
  have hcl := hdense V1 hV1o (fun z hz => hz.1.2.2) ⟨hxX, hxV1⟩
  obtain ⟨r, hr⟩ : (regLocus (X ∩ V1)).Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    rw [hemp, closure_empty] at hcl
    exact hcl
  obtain ⟨hrX, e, A', O, V', g, hO, hV', hrV', hg, hA'g, hXV'⟩ := hr
  have hgX : ∀ t ∈ O, g t ∈ X ∩ V1 := fun t ht => by
    have : g t ∈ X ∩ V1 ∩ V' := hXV' ▸ mem_image_of_mem g ht
    exact this.1
  have hN12 : ∀ z ∈ V1, z ∈ N1 ∩ N2 := fun z hz => interior_subset hz.1.2.1
  have hchart : X ∩ (V1 ∩ V') = g '' O := by rw [← hXV']; exact (inter_assoc X V1 V').symm
  have hde : d ≤ e := hdimN r ⟨hrX.1, (hN12 r hrX.2).1⟩ e A' O (V1 ∩ V') g hO (hV1o.inter hV')
    ⟨hrX.2, hrV'⟩ hg hA'g hchart
  have hφ : DifferentiableOn ℂ (fun y => A (g y)) O :=
    A.differentiable.comp_differentiableOn hg.differentiableOn
  have hisoC : ∀ t ∈ O, ∃ W ∈ 𝓝 t, ∀ v ∈ W, v ∈ O → A (g v) = A (g t) → v = t := by
    intro t ht
    obtain ⟨W, hW, hiW⟩ := hisoX (g t) ⟨(hgX t ht).1, (hN12 _ (hgX t ht).2).2⟩
    refine ⟨g ⁻¹' W, (hg t ht).continuousAt.preimage_mem_nhds hW, fun v hvW hvO hv => ?_⟩
    have hgv := hiW (g v) ⟨(hgX v hvO).1, hvW⟩ hv
    rw [← hA'g v hvO, ← hA'g t ht, hgv]
  obtain ⟨y0, hy0O, hy0r⟩ : r ∈ g '' O := hXV' ▸ ⟨hrX, hrV'⟩
  have hed : e ≤ d := le_of_isolated_fibres hfi hO ⟨y0, hy0O⟩ hφ hisoC
  obtain rfl : e = d := le_antisymm hed hde
  have hop := hopen e O (fun y => A (g y)) y0 hO hy0O hφ (hisoC y0 hy0O) O (hO.mem_nhds hy0O)
  have hzero : ∀ y ∈ (fun y => A (g y)) '' O, h y = 0 := by
    rintro _ ⟨t, ht, rfl⟩
    exact hV (hgX t ht).2.1.1 (hgX t ht).1
  have hAr : A (g y0) ∈ ball (A x) ε := (hgX y0 hy0O).2.2
  have hEq : EqOn h 0 (ball (A x) ε) :=
    hhb.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected hAr
      (Filter.mem_of_superset hop fun y hy => hzero y hy)
  filter_upwards [ball_mem_nhds (A x) hε] with y hy using hEq hy

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter Set

theorem isRegularPointOf_ball {d : ℕ} (c : Fin d → ℂ) (ε : ℝ) :
    ∀ y ∈ ball c ε, IsRegularPointOf (ball c ε) y := fun y hy =>
  ⟨hy, d, ContinuousLinearMap.id ℂ _, ball c ε, ball c ε, id, isOpen_ball, isOpen_ball, hy,
    analyticOnNhd_id, fun _ _ => rfl, by simp⟩

theorem IrreducibleGermPointsOffDiscriminant.proof (hPF : IrreducibleGermPrimitiveForm.Statement)
    (hSh : PrimitiveFormSheetedOffDiscriminant.Statement) (hNear : PrimitiveFormSheetedPointsNear.Statement)
    (hConn : ManifoldZerosComplementConnected.Statement) :
    IrreducibleGermPointsOffDiscriminant.Statement := by
  intro σ _ X x d A hX hirr hiso hinj
  obtain ⟨ℓ, N, a, δ, q, ha, hδ, hq, hδ0, hp, hsep, hqz⟩ := hPF σ X x d A hX hirr hiso hinj
  obtain ⟨M, hM, hMsh⟩ := hSh σ X x d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hp hsep hqz
  have hnear := hNear σ X x d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hp hsep hqz
  refine ⟨δ, hδ, hδ0, fun W hW => ?_⟩
  obtain ⟨W₀, hW₀, hiso'⟩ := hiso
  obtain ⟨Nn, k, f, hNo, hxN, hf, hXN⟩ := hX
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (inter_mem hW hM) (inter_mem hW₀ (hNo.mem_nhds hxN)))
  have hr2 : 0 < r / 2 := half_pos hr
  have hcb : closedBall x (r / 2) ⊆ (W ∩ M) ∩ (W₀ ∩ Nn) := (closedBall_subset_ball (half_lt_self hr)).trans hrsub

  set K : Set (σ → ℂ) := closedBall x (r / 2) ∩ ⋂ i, (closedBall x (r / 2) ∩ f i ⁻¹' {0}) with hK
  have hKc : IsCompact K := by
    refine (isCompact_closedBall x (r / 2)).of_isClosed_subset ?_ inter_subset_left
    refine isClosed_closedBall.inter (isClosed_iInter fun i => ?_)
    exact ((hf i).continuousOn.mono fun z hz => (hcb hz).2.2).preimage_isClosed_of_isClosed
      isClosed_closedBall isClosed_singleton
  have hKmem : ∀ z, z ∈ K ↔ z ∈ closedBall x (r / 2) ∧ z ∈ X := by
    intro z
    simp only [hK, mem_inter_iff, mem_iInter, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hz, h0⟩
      have : z ∈ {z | z ∈ Nn ∧ ∀ i, f i z = 0} := ⟨(hcb hz).2.2, fun i => (h0 i).2⟩
      rw [← hXN] at this
      exact ⟨hz, this.1⟩
    · rintro ⟨hz, hzX⟩
      have : z ∈ X ∩ Nn := ⟨hzX, (hcb hz).2.2⟩
      rw [hXN] at this
      exact ⟨hz, fun i => ⟨hz, this.2 i⟩⟩
  have hSc : IsCompact (K ∩ sphere x (r / 2)) := hKc.inter_right isClosed_sphere
  have hAS : A x ∉ A '' (K ∩ sphere x (r / 2)) := by
    rintro ⟨z, ⟨hzK, hzs⟩, hAz⟩
    have hzx : z = x := hiso' z ⟨((hKmem z).mp hzK).2, (hcb ((hKmem z).mp hzK).1).2.1⟩ hAz
    rw [hzx, mem_sphere, dist_self] at hzs
    exact hr2.ne hzs
  obtain ⟨ε₁, hε₁, hε₁S⟩ := Metric.isOpen_iff.mp (hSc.image A.continuous).isClosed.isOpen_compl (A x) hAS
  obtain ⟨ε₂, hε₂, hε₂a⟩ := hδ.exists_ball_analyticOnNhd
  set D := ball (A x) (min ε₁ ε₂) with hD
  have hε : 0 < min ε₁ ε₂ := lt_min hε₁ hε₂
  have hDa : AnalyticOnNhd ℂ δ D := hε₂a.mono (ball_subset_ball (min_le_right _ _))

  set T := D \ {y | δ y = 0} with hT
  have hTo : IsOpen T := hDa.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
  have hTc : IsPreconnected T := by
    refine hConn (Fin d) D δ (convex_ball _ _).isPreconnected (isRegularPointOf_ball _ _) hDa ?_
    obtain ⟨y, hy0, hyD⟩ := ((Filter.not_eventually.mp hδ0).and_eventually (ball_mem_nhds _ hε)).exists
    exact ⟨y, hyD, hy0⟩

  set u : Set (Fin d → ℂ) := T ∩ A '' (X ∩ ball x (r / 2)) with hu
  have huo : IsOpen u := by
    refine isOpen_iff_mem_nhds.mpr ?_
    rintro y ⟨hyT, z, ⟨hzX, hzb⟩, rfl⟩
    obtain ⟨O, V, g, hO, hV, hzV, hg, hAg, hXV⟩ := hMsh z ⟨hzX, (hcb (ball_subset_closedBall hzb)).1.2⟩ hyT.2
    obtain ⟨t₀, ht₀, hgt₀⟩ : z ∈ g '' O := hXV ▸ ⟨hzX, hzV⟩
    have hAz : A z = t₀ := by rw [← hgt₀]; exact hAg t₀ ht₀
    rw [hAz] at hyT ⊢
    have hpre : g ⁻¹' (V ∩ ball x (r / 2)) ∈ 𝓝 t₀ :=
      (hg t₀ ht₀).continuousAt.preimage_mem_nhds ((hV.inter isOpen_ball).mem_nhds (hgt₀ ▸ ⟨hzV, hzb⟩))
    filter_upwards [hTo.mem_nhds hyT, hO.mem_nhds ht₀, hpre] with t ht htO htg
    have hgX : g t ∈ X ∩ V := hXV ▸ ⟨t, htO, rfl⟩
    exact ⟨ht, g t, ⟨hgX.1, htg.2⟩, hAg t htO⟩
  have hune : (T ∩ u).Nonempty := by
    have hU : ball x (r / 2) ∩ A ⁻¹' D ∈ 𝓝 x :=
      inter_mem (ball_mem_nhds x hr2) (A.continuous.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hε))
    obtain ⟨z, ⟨hzX, hzb, hzD⟩, hδz, -⟩ := hnear _ hU
    exact ⟨A z, ⟨hzD, hδz⟩, ⟨hzD, hδz⟩, z, ⟨hzX, hzb⟩, rfl⟩
  have hucl : closure u ∩ T ⊆ u := by
    rintro y ⟨hycl, hyT⟩
    have hsubK : u ⊆ A '' K := by
      rintro _ ⟨-, z, ⟨hzX, hzb⟩, rfl⟩
      exact ⟨z, (hKmem z).mpr ⟨ball_subset_closedBall hzb, hzX⟩, rfl⟩
    obtain ⟨z, hzK, rfl⟩ := (hKc.image A.continuous).isClosed.closure_subset_iff.mpr hsubK hycl
    obtain ⟨hzcb, hzX⟩ := (hKmem z).mp hzK
    have hzb : z ∈ ball x (r / 2) := by
      refine mem_ball.mpr (lt_of_le_of_ne (mem_closedBall.mp hzcb) fun hzs => ?_)
      exact hε₁S (ball_subset_ball (min_le_left _ _) hyT.1) ⟨z, ⟨hzK, mem_sphere.mpr hzs⟩, rfl⟩
    exact ⟨hyT, z, ⟨hzX, hzb⟩, rfl⟩
  have hTu : T ⊆ u := hTc.subset_of_closure_inter_subset huo hune hucl
  filter_upwards [ball_mem_nhds (A x) hε] with y hy hδy
  obtain ⟨-, z, ⟨hzX, hzb⟩, hzy⟩ := hTu ⟨hy, hδy⟩
  exact ⟨z, ⟨hzX, (hcb (ball_subset_closedBall hzb)).1.1⟩, hzy⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

theorem exists_lastCoord_ne_zero_of_mem_nhds {σ : Type} {U : Set (Option σ → ℂ)} {w : Option σ → ℂ}
    (hU : U ∈ 𝓝 w) : ∃ v ∈ U, v none ≠ 0 := by
  classical
  let g : ℂ → Option σ → ℂ := fun s => Function.update w none s
  have hg : Continuous g := by
    refine continuous_pi fun o => ?_
    cases o with
    | none => simpa [g] using continuous_id'
    | some i => simpa [g] using continuous_const
  have hgw : g (w none) = w := Function.update_eq_self none w
  have hev : ∀ᶠ s in 𝓝 (w none), g s ∈ U := by
    have := hg.tendsto (w none)
    rw [hgw] at this
    exact this hU
  have hne : ∀ᶠ s in 𝓝[≠] (w none), s ≠ 0 := by
    by_cases h0 : w none = 0
    · rw [h0]; exact self_mem_nhdsWithin
    · exact nhdsWithin_le_nhds (isOpen_ne.mem_nhds h0)
  obtain ⟨s, hs1, hs2⟩ := (((hev.filter_mono nhdsWithin_le_nhds) : ∀ᶠ s in 𝓝[≠] (w none), g s ∈ U).and hne).exists
  exact ⟨g s, hs1, by simpa [g] using hs2⟩

theorem GeneralLinearCoordinates.proof : GeneralLinearCoordinates.Statement := by
  classical
  intro σ _ f hf hnz
  obtain ⟨r, hr, hfr⟩ := hf.exists_ball_analyticOnNhd

  obtain ⟨w, hwb, hfw⟩ : ∃ w ∈ Metric.ball (0 : Option σ → ℂ) r, f w ≠ 0 := by
    by_contra h
    push Not at h
    exact hnz (Filter.mem_of_superset (Metric.ball_mem_nhds _ hr) fun x hx => h x hx)
  have hUopen : IsOpen (Metric.ball (0 : Option σ → ℂ) r ∩ f ⁻¹' {z | z ≠ 0}) :=
    hfr.continuousOn.isOpen_inter_preimage Metric.isOpen_ball isOpen_ne
  obtain ⟨v, ⟨hvb, hfv⟩, hvt⟩ := exists_lastCoord_ne_zero_of_mem_nhds (hUopen.mem_nhds ⟨hwb, hfw⟩)
  replace hfv : f v ≠ 0 := hfv

  let e : Option σ → ℂ := Pi.single none 1
  let L : (Option σ → ℂ) →ₗ[ℂ] (Option σ → ℂ) :=
    LinearMap.id + (LinearMap.proj (R := ℂ) (φ := fun _ : Option σ => ℂ) none).smulRight (v - e)
  have hL : ∀ x, L x = x + x none • (v - e) := fun x => rfl
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 : (L x) none = 0 := by rw [hx]; rfl
    have hnone : x none = 0 := by
      rw [hL] at h1
      simp [e] at h1
      have h2 : x none * v none = 0 := by linear_combination h1
      exact (mul_eq_zero.mp h2).resolve_right hvt
    rw [hL, hnone, zero_smul, add_zero] at hx
    exact hx
  let A : (Option σ → ℂ) ≃L[ℂ] (Option σ → ℂ) :=
    (LinearEquiv.ofInjectiveEndo L hLinj).toContinuousLinearEquiv
  have hA : ∀ t : ℂ, A (pointWithLast 0 t) = t • v := by
    intro t
    show L (pointWithLast 0 t) = t • v
    rw [hL]
    funext o
    cases o with
    | none => simp [pointWithLast, e]; ring
    | some i => simp [pointWithLast, e]
  refine ⟨A, ?_⟩
  have hfun : (fun t => f (A (pointWithLast 0 t))) = fun t : ℂ => f (t • v) := by
    funext t; rw [hA]
  rw [hfun]

  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr fun h => hvt (by rw [h]; rfl)
  have hvr : ‖v‖ < r := by simpa using hvb
  set R := r / ‖v‖
  have hR1 : (1 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right, norm_one]
    exact (one_lt_div hv0).mpr hvr
  have hR0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := Metric.mem_ball_self (lt_trans one_pos
    ((one_lt_div hv0).mpr hvr))
  have han : AnalyticOnNhd ℂ (fun t : ℂ => f (t • v)) (Metric.ball (0 : ℂ) R) := by
    intro t ht
    have htv : t • v ∈ Metric.ball (0 : Option σ → ℂ) r := by
      rw [Metric.mem_ball, dist_zero_right, norm_smul]
      rw [Metric.mem_ball, dist_zero_right] at ht
      calc ‖t‖ * ‖v‖ < R * ‖v‖ := mul_lt_mul_of_pos_right ht hv0
        _ = r := div_mul_cancel₀ r hv0.ne'
    have hs : AnalyticAt ℂ (fun s : ℂ => s • v) t := analyticAt_id.smul analyticAt_const
    show AnalyticAt ℂ (f ∘ fun s : ℂ => s • v) t
    exact AnalyticAt.comp (f := fun s : ℂ => s • v) (x := t) (hfr _ htv) hs
  have hnot : ¬ (∀ᶠ t in 𝓝 (0 : ℂ), f (t • v) = 0) := by
    intro h
    have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected hR0 h hR1
    simp at this
    exact hfv this
  have hne : analyticOrderAt (fun t : ℂ => f (t • v)) 0 ≠ ⊤ := fun h =>
    hnot (analyticOrderAt_eq_top.mp h)
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hne
  exact ⟨d, hd.symm⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem PrimitiveFormSheetedOffDiscriminant.proof (hcut : PrimitiveFormSheetedLocusCutOut.Statement)
    (hnear : PrimitiveFormSheetedPointsNear.Statement) : PrimitiveFormSheetedOffDiscriminant.Statement := by
  intro σ _ X w d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hP hsep hQ
  obtain ⟨c, e, hc, he, hce, hsh⟩ := hcut σ X w d A hX hiso ℓ N a δ q ha hδ hq hδ0 hP hsep hQ
  rcases hirr.2 c e hc he hce with hc0 | he0
  · exact ⟨_, hc0.and hsh, fun y hy hyδ => ((hy.2.2 hy.1 hyδ).1).2 (hy.2.1 hy.1)⟩
  · exfalso
    obtain ⟨z, hz, hzδ, hzs⟩ :=
      hnear σ X w d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hP hsep hQ _ (he0.and hsh)
    exact (hz.2.2 hz.1 hzδ).2 hzs (hz.2.1 hz.1)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem PrimitiveFormWindow.proof : PrimitiveFormWindow.Statement := by
  intro σ _ X w d A hX hiso ℓ N a δ q ha hδ hq hp hsep hrel
  obtain ⟨N₀, k, f, hN₀o, hwN₀, hfa, hXN⟩ := hX
  obtain ⟨W₀, hW₀, hW₀iso⟩ := hiso
  have hev := (show ∀ᶠ z in 𝓝 w, z ∈ N₀ from hN₀o.mem_nhds hwN₀).and
    ((show ∀ᶠ z in 𝓝 w, z ∈ W₀ from hW₀).and (hp.and (Filter.eventually_all.2 hrel)))
  obtain ⟨ε, hε, hεs⟩ := Metric.nhds_basis_closedBall.eventually_iff.1 hev
  set K : Set (σ → ℂ) := Metric.sphere w ε ∩ (fun z i => f i z) ⁻¹' {0} with hK
  have hsN : Metric.sphere w ε ⊆ N₀ := fun z hz => (hεs (Metric.sphere_subset_closedBall hz)).1
  have hKc : IsCompact K := by
    refine (isCompact_sphere w ε).of_isClosed_subset ?_ Set.inter_subset_left
    refine ContinuousOn.preimage_isClosed_of_isClosed ?_ Metric.isClosed_sphere isClosed_singleton
    exact continuousOn_pi.2 fun i => ((hfa i).continuousOn).mono hsN
  have hKX : ∀ z ∈ K, z ∈ X := by
    intro z hz
    have : z ∈ X ∩ N₀ := by
      rw [hXN]
      refine ⟨hsN hz.1, fun i => ?_⟩
      have := congrFun (Set.mem_singleton_iff.1 hz.2) i
      simpa using this
    exact this.1
  have hXK : ∀ z ∈ X, z ∈ Metric.sphere w ε → z ∈ K := by
    intro z hzX hzs
    refine ⟨hzs, ?_⟩
    have : z ∈ X ∩ N₀ := ⟨hzX, hsN hzs⟩
    rw [hXN] at this
    exact Set.mem_singleton_iff.2 (funext this.2)
  have hAK : A w ∉ A '' K := by
    rintro ⟨z, hzK, hAz⟩
    have hzw := (hεs (Metric.sphere_subset_closedBall hzK.1)).2.1
    have hzeq := hW₀iso z ⟨hKX z hzK, hzw⟩ hAz
    have h1 := hzK.1
    rw [hzeq, Metric.mem_sphere, dist_self] at h1
    exact hε.ne h1
  have hclo : IsClosed (A '' K) := (hKc.image A.continuous).isClosed
  have hev2 := (show ∀ᶠ y in 𝓝 (A w), y ∈ (A '' K)ᶜ from hclo.isOpen_compl.mem_nhds hAK).and
    ((Filter.eventually_all.2 fun j => (ha j).eventually_analyticAt).and
      (hδ.eventually_analyticAt.and
        ((Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
          (hq i j).eventually_analyticAt).and hsep)))
  obtain ⟨ρ, hρ, hρs⟩ := Metric.nhds_basis_ball.eventually_iff.1 hev2
  refine ⟨Metric.ball w ε, Metric.ball (A w) ρ, N₀, k, f, Metric.isOpen_ball, Metric.mem_ball_self hε,
    Metric.isOpen_ball, convex_ball _ _, Metric.mem_ball_self hρ, hN₀o, ?_, hfa, hXN, ?_, ?_, ?_,
    fun j y hy => (hρs hy).2.1 j, fun y hy => (hρs hy).2.2.1, fun i j y hy => (hρs hy).2.2.2.1 i j,
    fun y hy => (hρs hy).2.2.2.2⟩
  · rw [closure_ball w hε.ne']
    exact fun z hz => (hεs hz).1
  · rintro z ⟨hzX, hzc⟩ hzB
    rw [closure_ball w hε.ne'] at hzc
    rcases (Metric.mem_closedBall.1 hzc).lt_or_eq with h | h
    · exact Metric.mem_ball.2 h
    · exact absurd ⟨z, hXK z hzX (Metric.mem_sphere.2 h), rfl⟩ (hρs hzB).1
  · rintro z ⟨hzX, hzW⟩
    exact (hεs (Metric.ball_subset_closedBall hzW)).2.2.1 hzX
  · rintro i z ⟨hzX, hzW⟩
    exact (hεs (Metric.ball_subset_closedBall hzW)).2.2.2 i hzX

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
