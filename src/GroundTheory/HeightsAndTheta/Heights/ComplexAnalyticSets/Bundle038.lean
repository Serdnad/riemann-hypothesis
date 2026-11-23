module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle014
public import Mathlib.Algebra.MvPolynomial.Funext
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle016
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle023
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
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Analytic.Uniqueness

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

theorem VanishNearPoint.proof (hOpen : FiniteMapOpen.Statement) : VanishNearPoint.Statement := by
  classical
  intro n J f x hJ hx hf
  by_contra hfJ
  have : Nontrivial (MvPolynomial (Fin n) ℂ ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ.ne_top
  obtain ⟨d, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ (MvPolynomial (Fin n) ℂ ⧸ J)
  choose p hp using fun i => Ideal.Quotient.mk_surjective (g (X i))
  have hg : g = (Ideal.Quotient.mkₐ ℂ J).comp (aeval p) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [hp]
  subst hg
  let _ := ((Ideal.Quotient.mkₐ ℂ J).comp (aeval p)).toRingHom.toAlgebra
  have hint : IsIntegral (MvPolynomial (Fin d) ℂ) (Ideal.Quotient.mk J f) :=
    RingHom.IsIntegral.of_finite hfin _
  have hf0 : Ideal.Quotient.mk J f ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨h, hh, hh0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Ideal.comap_ne_bot_of_integral_mem hf0 (Ideal.mem_span_singleton_self _) hint)
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hh
  obtain ⟨a, ha⟩ := hh
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hJmem : aeval p h - q * f ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, sub_eq_zero]
    exact ha.symm

  have hval : ∀ z ∈ zeroLocus J, eval (fun i => eval z (p i)) h = eval z q * eval z f := by
    intro z hz
    have h1 := hz _ hJmem
    rw [map_sub, map_mul, sub_eq_zero] at h1
    rw [← h1]
    have h2 := DFunLike.congr_fun (MvPolynomial.comp_aeval (R := ℂ) (aeval z : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ) (f := p)) h
    rw [AlgHom.comp_apply] at h2
    exact h2.symm
  have hV := hOpen n d J p hJ hinj hfin x hx _ hf
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  apply hh0
  refine MvPolynomial.funext_set (fun i => Metric.ball (eval x (p i)) ε)
    (fun i => infinite_of_mem_nhds _ (Metric.ball_mem_nhds _ hε)) fun w hw => ?_
  rw [← ball_pi _ hε] at hw
  obtain ⟨z, ⟨hz, hzU⟩, rfl⟩ := hball hw
  rw [hval z hz, hzU hz, mul_zero, map_zero]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter MeasureTheory

theorem exists_clm_ne_zero_of_countable {σ : Type} [Fintype σ] {T : Set (σ → ℂ)} (hT : T.Countable)
    (h0 : (0 : σ → ℂ) ∉ T) : ∃ ℓ : (σ → ℂ) →L[ℂ] ℂ, ∀ u ∈ T, ℓ u ≠ 0 := by
  classical
  let φ : (σ → ℂ) → ((σ → ℂ) →ₗ[ℝ] ℂ) := fun u =>
    { toFun := fun v => ∑ i, v i * u i
      map_add' := fun a b => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c a => by simp [Finset.mul_sum, mul_assoc] }
  have hφ : ∀ u v, φ u v = ∑ i, v i * u i := fun _ _ => rfl
  have hker : ∀ u ∈ T, volume (LinearMap.ker (φ u) : Set (σ → ℂ)) = 0 := by
    intro u hu
    refine Measure.addHaar_submodule volume _ fun htop => ?_
    obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra h
      push Not at h
      exact h0 (by rwa [show u = 0 from funext h] at hu)
    have hm : Pi.single i 1 ∈ LinearMap.ker (φ u) := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hφ] at hm
    simp [Pi.single_apply] at hm
    exact hi hm
  have hnull : volume (⋃ u ∈ T, (LinearMap.ker (φ u) : Set (σ → ℂ))) = 0 :=
    (measure_biUnion_null_iff hT).2 hker
  obtain ⟨v, hv⟩ : ∃ v, v ∉ ⋃ u ∈ T, (LinearMap.ker (φ u) : Set (σ → ℂ)) := by
    by_contra h
    push Not at h
    have hu : (Set.univ : Set (σ → ℂ)) ⊆ ⋃ u ∈ T, (LinearMap.ker (φ u) : Set (σ → ℂ)) := fun x _ => h x
    have hpos := isOpen_univ.measure_pos (volume : Measure (σ → ℂ)) Set.univ_nonempty
    exact hpos.ne' (measure_mono_null hu hnull)
  refine ⟨∑ i, v i • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i, fun u hu => ?_⟩
  have hvu : φ u v ≠ 0 := fun h => hv (Set.mem_biUnion hu (LinearMap.mem_ker.2 h))
  rw [hφ] at hvu
  simpa [ContinuousLinearMap.sum_apply] using hvu

theorem ParametrisationSheetsConnected.proof (h₁ : SheetPieceProductAnalytic.Statement)
    (h₂ : SheetPieceReachesCentre.Statement) : ParametrisationSheetsConnected.Statement := by
  classical
  intro σ _ X w B d A D δ N hP hirr
  obtain ⟨hB, hwXB, hD, -, hmaps, -, -, -, -, hcard, -, hdense⟩ := id hP
  set S := {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} with hS
  by_contra hnc
  rw [IsPreconnected] at hnc
  push Not at hnc
  obtain ⟨u, v, hu, hv, hSuv, hSu, hSv, hdisj⟩ := hnc
  have hdisj' : S ∩ (v ∩ u) = ∅ := by rwa [Set.inter_comm v u]
  have hSvu : S ⊆ v ∪ u := by rwa [Set.union_comm]
  have hwu := h₂ σ X w B d A D δ N u v hP hu hv hSuv hdisj hSu
  have hwv := h₂ σ X w B d A D δ N v u hP hv hu hSvu hdisj' hSv
  obtain ⟨p, hpS, hpw⟩ := mem_closure_iff_seq_limit.1 hwu
  obtain ⟨q, hqS, hqw⟩ := mem_closure_iff_seq_limit.1 hwv

  have hfin : ∀ (U' : Set (σ → ℂ)), ∀ x ∈ S, {x' | x' ∈ X ∩ B ∧ x' ∈ U' ∧ A x' = A x}.Finite :=
    fun U' x hx => (Set.finite_of_encard_eq_coe (hcard (A x) (hmaps hx.1) hx.2)).subset
      fun x' hx' => ⟨hx'.1, hx'.2.2⟩
  set T : Set (σ → ℂ) :=
    (⋃ n, (fun x' => p n - x') '' {x' | x' ∈ X ∩ B ∧ x' ∈ v ∧ A x' = A (p n)}) ∪
      ⋃ n, (fun x' => q n - x') '' {x' | x' ∈ X ∩ B ∧ x' ∈ u ∧ A x' = A (q n)} with hT
  have hTc : T.Countable :=
    (Set.countable_iUnion fun n => ((hfin v (p n) (hpS n).1).image _).countable).union
      (Set.countable_iUnion fun n => ((hfin u (q n) (hqS n).1).image _).countable)
  have hT0 : (0 : σ → ℂ) ∉ T := by
    have key : ∀ (r : σ → ℂ) (U₁ U₂ : Set (σ → ℂ)), r ∈ S ∩ U₁ → S ∩ (U₁ ∩ U₂) = ∅ →
        ∀ x' ∈ {x' | x' ∈ X ∩ B ∧ x' ∈ U₂ ∧ A x' = A r}, r - x' ≠ 0 := by
      intro r U₁ U₂ hr hd x' hx' h0
      have hrx : r = x' := sub_eq_zero.1 h0
      have hx'S : x' ∈ S := ⟨hx'.1, by rw [hx'.2.2]; exact hr.1.2⟩
      exact (Set.eq_empty_iff_forall_notMem.1 hd x') ⟨hx'S, hrx ▸ hr.2, hx'.2.1⟩
    rintro (h | h) <;> obtain ⟨n, x', hx', hx0⟩ := Set.mem_iUnion.1 h
    · exact key (p n) u v (hpS n) hdisj x' hx' hx0
    · exact key (q n) v u (hqS n) hdisj' x' hx' hx0
  obtain ⟨ℓ, hℓ⟩ := exists_clm_ne_zero_of_countable hTc hT0
  obtain ⟨f, hfan, hfeq⟩ := h₁ σ X w B d A D δ N u v ℓ hP hu hv hSuv hdisj
  obtain ⟨g, hgan, hgeq⟩ := h₁ σ X w B d A D δ N v u ℓ hP hv hu hSvu hdisj'

  have hzero : ∀ (U' : Set (σ → ℂ)) (F : (σ → ℂ) → ℂ),
      (∀ z, A z ∈ D → δ (A z) ≠ 0 →
        F z = ∏ᶠ x ∈ {x | x ∈ X ∩ B ∧ x ∈ U' ∧ A x = A z}, (ℓ z - ℓ x)) →
      ∀ x ∈ S, x ∈ U' → F x = 0 := by
    intro U' F hF x hx hxU
    rw [hF x (hmaps hx.1) hx.2, finprod_mem_eq_finite_toFinset_prod _ (hfin U' x hx)]
    exact Finset.prod_eq_zero ((hfin U' x hx).mem_toFinset.2 ⟨hx.1, hxU, rfl⟩) (sub_self _)

  have hne : ∀ (U' : Set (σ → ℂ)) (F : (σ → ℂ) → ℂ) (r : σ → ℂ),
      (∀ z, A z ∈ D → δ (A z) ≠ 0 →
        F z = ∏ᶠ x ∈ {x | x ∈ X ∩ B ∧ x ∈ U' ∧ A x = A z}, (ℓ z - ℓ x)) → r ∈ S →
      (∀ x' ∈ {x' | x' ∈ X ∩ B ∧ x' ∈ U' ∧ A x' = A r}, r - x' ∈ T) → F r ≠ 0 := by
    intro U' F r hF hr hrT
    rw [hF r (hmaps hr.1) hr.2, finprod_mem_eq_finite_toFinset_prod _ (hfin U' r hr)]
    refine Finset.prod_ne_zero_iff.2 fun x' hx' => ?_
    rw [← map_sub]
    exact hℓ _ (hrT x' ((hfin U' r hr).mem_toFinset.1 hx'))
  have hfq : ∀ n, f (q n) ≠ 0 := fun n => hne u f (q n) hfeq (hqS n).1
    fun x' hx' => Or.inr (Set.mem_iUnion.2 ⟨n, x', hx', rfl⟩)
  have hgp : ∀ n, g (p n) ≠ 0 := fun n => hne v g (p n) hgeq (hpS n).1
    fun x' hx' => Or.inl (Set.mem_iUnion.2 ⟨n, x', hx', rfl⟩)

  have hprod : ∀ z ∈ X ∩ B, f z * g z = 0 := by
    intro z hz
    have hc : ContinuousAt (fun z => f z * g z) z :=
      (hfan z (hmaps hz)).continuousAt.mul (hgan z (hmaps hz)).continuousAt
    have := mem_closure_iff_nhdsWithin_neBot.1 (hdense hz)
    have h2 : (fun z => f z * g z) =ᶠ[𝓝[S] z] fun _ => 0 :=
      eventually_nhdsWithin_of_forall fun x hx => by
        rcases hSuv hx with hxu | hxv
        · simp [hzero u f hfeq x hx hxu]
        · simp [hzero v g hgeq x hx hxv]
    exact tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' h2.symm)
  have hw : A w ∈ D := hmaps hwXB
  have hev : ∀ᶠ z in 𝓝 w, z ∈ X → f z * g z = 0 := by
    filter_upwards [hB.mem_nhds hwXB.2] with z hzB hzX using hprod z ⟨hzX, hzB⟩
  rcases hirr.2 f g (hfan w hw) (hgan w hw) hev with hf0 | hg0
  · obtain ⟨n, hn⟩ := (hqw.eventually hf0).exists
    exact hfq n (hn (hqS n).1.1.1)
  · obtain ⟨n, hn⟩ := (hpw.eventually hg0).exists
    exact hgp n (hn (hpS n).1.1.1)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem UnbranchedFibreSections.proof : UnbranchedFibreSections.Statement := by
  intro σ _ X w B d A D δ N hP y₀ hy₀ hδ₀
  obtain ⟨_, _, hD, _, _, hprop, _, hδan, _, hcard, hchart, _⟩ := hP
  have hF0 : {x | x ∈ X ∩ B ∧ A x = y₀}.encard = N := hcard y₀ hy₀ hδ₀
  have hfin : {x | x ∈ X ∩ B ∧ A x = y₀}.Finite := Set.finite_of_encard_eq_coe hF0
  have ht : hfin.toFinset.card = N := by
    have h := hfin.encard_eq_coe_toFinset_card
    rw [hF0] at h
    exact_mod_cast h.symm
  let e : Fin N ≃ hfin.toFinset := (Finset.equivFinOfCardEq ht).symm
  have he : ∀ i, (e i : σ → ℂ) ∈ X ∩ B ∧ A (e i) = y₀ := fun i => hfin.mem_toFinset.mp (e i).2
  have hc : ∀ i : Fin N, ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ (e i : σ → ℂ) ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧
        X ∩ B ∩ V = g '' O := fun i => hchart _ (he i).1 (by rw [(he i).2]; exact hδ₀)
  choose O V g hO hV hxV hg hAg hXV using hc
  have hy₀O : ∀ i, y₀ ∈ O i := by
    intro i
    have hm : (e i : σ → ℂ) ∈ X ∩ B ∩ V i := ⟨(he i).1, hxV i⟩
    rw [hXV i] at hm
    obtain ⟨y', hy', hgy'⟩ := hm
    have h := hAg i y' hy'
    rw [hgy', (he i).2] at h
    rw [h]
    exact hy'
  obtain ⟨ρ, hρ, hρD⟩ := Metric.isOpen_iff.mp hD y₀ hy₀
  have hKD : Metric.closedBall y₀ (ρ / 2) ⊆ D :=
    (Metric.closedBall_subset_ball (by linarith)).trans hρD
  set C := {x | x ∈ X ∩ B ∧ A x ∈ Metric.closedBall y₀ (ρ / 2)} with hCdef
  have hC : IsCompact C := hprop _ hKD (isCompact_closedBall _ _)
  have hC' : IsCompact (C \ ⋃ i, V i) := hC.diff (isOpen_iUnion hV)
  have hE : IsClosed (A '' (C \ ⋃ i, V i)) := (hC'.image A.continuous).isClosed
  have hy₀E : y₀ ∉ A '' (C \ ⋃ i, V i) := by
    rintro ⟨x, ⟨⟨hxXB, _⟩, hxV'⟩, hAx⟩
    have hxF : x ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨hxXB, hAx⟩
    apply hxV'
    refine Set.mem_iUnion.mpr ⟨e.symm ⟨x, hxF⟩, ?_⟩
    simpa using hxV (e.symm ⟨x, hxF⟩)
  have hnhds : Metric.ball y₀ (ρ / 2) ∩ (A '' (C \ ⋃ i, V i))ᶜ ∩ (⋂ i, O i) ∩ {y | δ y ≠ 0} ∈ 𝓝 y₀ := by
    refine Filter.inter_mem (Filter.inter_mem (Filter.inter_mem
      (Metric.ball_mem_nhds _ (by linarith)) (hE.isOpen_compl.mem_nhds hy₀E)) ?_) ?_
    · exact Filter.iInter_mem.mpr fun i => (hO i).mem_nhds (hy₀O i)
    · exact (hδan y₀ hy₀).continuousAt.eventually_ne hδ₀
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hnhds
  have hrD : Metric.ball y₀ r ⊆ D := fun y hy =>
    hρD (Metric.ball_subset_ball (by linarith) (hrsub hy).1.1.1)
  refine ⟨r, g, hr, hrD, fun y hy => (hrsub hy).2,
    fun i y hy => hg i y (Set.mem_iInter.mp (hrsub hy).1.2 i), ?_⟩
  intro y hy
  obtain ⟨⟨⟨hyb, hyE⟩, hyO⟩, hyδ⟩ := hrsub hy
  have hyO' : ∀ i, y ∈ O i := Set.mem_iInter.mp hyO
  have hrange : {x | x ∈ X ∩ B ∧ A x = y} = Set.range (fun i => g i y) := by
    ext x
    constructor
    · rintro ⟨hxXB, hAx⟩
      have hxC : x ∈ C := ⟨hxXB, by rw [hAx]; exact Metric.ball_subset_closedBall hyb⟩
      have hxU : x ∈ ⋃ i, V i := by
        by_contra hn
        exact hyE ⟨x, ⟨hxC, hn⟩, hAx⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxU
      have hm : x ∈ X ∩ B ∩ V i := ⟨hxXB, hi⟩
      rw [hXV i] at hm
      obtain ⟨y', hy', rfl⟩ := hm
      have h := hAg i y' hy'
      rw [hAx] at h
      exact ⟨i, by rw [h]⟩
    · rintro ⟨i, rfl⟩
      have hm : g i y ∈ g i '' O i := ⟨y, hyO' i, rfl⟩
      rw [← hXV i] at hm
      exact ⟨hm.1, hAg i y (hyO' i)⟩
  refine ⟨?_, hrange⟩
  classical
  have hN : (Set.range (fun i => g i y)).encard = N := by
    rw [← hrange]
    exact hcard y (hrD hy) hyδ
  have himg : Set.range (fun i => g i y) = ↑(Finset.univ.image (fun i => g i y)) := by
    simp
  rw [himg, Set.encard_coe_eq_coe_finsetCard] at hN
  have hcardeq : (Finset.univ.image (fun i => g i y)).card = (Finset.univ : Finset (Fin N)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact_mod_cast hN
  have hinj := Finset.card_image_iff.mp hcardeq
  intro i j hij
  exact hinj (Finset.mem_coe.mpr (Finset.mem_univ i)) (Finset.mem_coe.mpr (Finset.mem_univ j)) hij

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

def WeierstrassPolynomialDivision.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (d : ℕ) (c : Fin d → (σ → ℂ) → ℂ) (g : (Option σ → ℂ) → ℂ),
    (∀ j, AnalyticAt ℂ (c j) 0) → (∀ j, c j 0 = 0) → AnalyticAt ℂ g 0 →
    ∃ (q : (Option σ → ℂ) → ℂ) (a : Fin d → (σ → ℂ) → ℂ),
      AnalyticAt ℂ q 0 ∧ (∀ j, AnalyticAt ℂ (a j) 0) ∧
      ∀ᶠ x in 𝓝 (0 : Option σ → ℂ),
        g x = q x * weierstrassPolynomial c x + ∑ j : Fin d, a j (fun i => x (some i)) * x none ^ (j : ℕ)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

theorem BranchInverseOffHypersurface.proof (hinv : InjectiveHolomorphicInverse.Statement)
    (hproj : ProjectionInjectiveOffHypersurface.Statement) :
    BranchInverseOffHypersurface.Statement := by
  intro σ _ I k hI hk
  obtain ⟨h', hh', hloc⟩ := hproj σ I k hI hk
  refine ⟨h', hh', fun U φ ψ hU hφd hφi hφZ hψ => ?_⟩
  rintro _ ⟨⟨t, ht, rfl⟩, hz⟩
  obtain ⟨W, hWo, hzW, A, hA⟩ := hloc (φ t) (hφZ ht) hz
  have hU'o : IsOpen (U ∩ φ ⁻¹' W) := hφd.continuousOn.isOpen_inter_preimage hU hWo
  have hfd : DifferentiableOn ℂ (fun s => A (φ s)) (U ∩ φ ⁻¹' W) :=
    A.differentiable.differentiableOn.comp (hφd.mono Set.inter_subset_left) (Set.mapsTo_univ _ _)
  have hfi : Set.InjOn (fun s => A (φ s)) (U ∩ φ ⁻¹' W) := fun s hs s' hs' hss' =>
    hφi hs.1 hs'.1 (hA ⟨hφZ hs.1, hs.2⟩ ⟨hφZ hs'.1, hs'.2⟩ hss')
  obtain ⟨hOo, g, hgd, hgf⟩ := hinv k _ _ hU'o hfd hfi
  refine ⟨W ∩ A ⁻¹' ((fun s => A (φ s)) '' (U ∩ φ ⁻¹' W)), hWo.inter (hOo.preimage A.continuous),
    ⟨hzW, t, ⟨ht, hzW⟩, rfl⟩, fun y => g (A y), ?_, ?_⟩
  · exact hgd.comp A.differentiable.differentiableOn fun y hy => hy.2
  · rintro _ ⟨⟨⟨s, hs, rfl⟩, -⟩, hsW, -⟩
    show ψ (φ s) = g (A (φ s))
    rw [hψ s hs, hgf s ⟨hs, hsW⟩]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric

noncomputable section

def HolGermsDomain.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ), IsDomain (holGerms w)

theorem eventually_zero_or_of_mul_eventually_zero {σ : Type} [Fintype σ] {w : σ → ℂ}
    {f g : (σ → ℂ) → ℂ} (hf : AnalyticAt ℂ f w) (hg : AnalyticAt ℂ g w)
    (hfg : ∀ᶠ z in 𝓝 w, f z * g z = 0) :
    (∀ᶠ z in 𝓝 w, f z = 0) ∨ ∀ᶠ z in 𝓝 w, g z = 0 := by
  obtain ⟨r₁, hr₁, hf'⟩ := hf.exists_ball_analyticOnNhd
  obtain ⟨r₂, hr₂, hg'⟩ := hg.exists_ball_analyticOnNhd
  obtain ⟨r₃, hr₃, hfg'⟩ := Metric.eventually_nhds_iff_ball.1 hfg
  have hr : 0 < min r₁ (min r₂ r₃) := lt_min hr₁ (lt_min hr₂ hr₃)
  have hU1 : ball w (min r₁ (min r₂ r₃)) ⊆ ball w r₁ := ball_subset_ball (min_le_left _ _)
  have hU2 : ball w (min r₁ (min r₂ r₃)) ⊆ ball w r₂ :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
  have hU3 : ball w (min r₁ (min r₂ r₃)) ⊆ ball w r₃ :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))
  by_cases h : ∀ z ∈ ball w (min r₁ (min r₂ r₃)), f z = 0
  · left
    filter_upwards [ball_mem_nhds w hr] with x hx
    exact h x hx
  · right
    push Not at h
    obtain ⟨z, hz, hfz⟩ := h
    have hgz : g =ᶠ[𝓝 z] 0 := by
      have h1 : ∀ᶠ x in 𝓝 z, f x ≠ 0 := (hf' z (hU1 hz)).continuousAt.eventually_ne hfz
      have h2 : ∀ᶠ x in 𝓝 z, x ∈ ball w (min r₁ (min r₂ r₃)) := isOpen_ball.mem_nhds hz
      filter_upwards [h1, h2] with x hx1 hx2
      have h3 := hfg' x (hU3 hx2)
      simpa [hx1] using h3
    have hEq := (hg'.mono hU2).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball w _).isPreconnected hz hgz
    filter_upwards [ball_mem_nhds w hr] with x hx
    simpa using hEq hx

theorem HolGermsDomain.proof : HolGermsDomain.Statement := by
  intro σ _ w
  have : NoZeroDivisors (holGerms w) := by
    refine ⟨fun {a b} hab => ?_⟩
    obtain ⟨f, hf, hfa⟩ := a.2
    obtain ⟨g, hg, hgb⟩ := b.2
    have h0 : ((f * g : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) := by
      rw [Germ.coe_mul, hfa, hgb]
      exact congrArg Subtype.val hab
    have h1 : ∀ᶠ z in 𝓝 w, f z * g z = 0 := (Germ.coe_eq.1 h0).mono fun z hz => by simpa using hz
    rcases eventually_zero_or_of_mul_eventually_zero hf hg h1 with h | h
    · left
      apply Subtype.ext
      change (a : Germ (𝓝 w) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)
      rw [← hfa]
      exact Germ.coe_eq.2 (h.mono fun z hz => by simpa using hz)
    · right
      apply Subtype.ext
      change (b : Germ (𝓝 w) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)
      rw [← hgb]
      exact Germ.coe_eq.2 (h.mono fun z hz => by simpa using hz)
  exact NoZeroDivisors.to_isDomain _

instance holGerms_isDomain {σ : Type} [Fintype σ] (w : σ → ℂ) : IsDomain (holGerms w) :=
  HolGermsDomain.proof σ w

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def AnalyticGermsNoetherian.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ), IsNoetherianRing (holGerms w)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
