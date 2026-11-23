module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle009
public import Mathlib.Analysis.Analytic.Basic
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle071
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGraphAreaHolomorphic
import Mathlib.Algebra.Module.StablyFree.Basic
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle032
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle061
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle063
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle064
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle035
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle053
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle060
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric MeasureTheory
open scoped ENNReal NNReal

namespace ProperHolomorphicSurjective

theorem analyticOnNhd_of_differentiableOn {k m : ℕ} {U : Set (Fin k → ℂ)} {f : (Fin k → ℂ) → Fin m → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := by
  refine analyticOnNhd_pi_iff.2 fun j => ?_
  have hj : DifferentiableOn ℂ (fun t => f t j) U := differentiableOn_pi.1 hf j
  refine analyticOnNhd_of_continuousOn_of_separately hU hj.continuousOn fun w hw i => ?_
  have hw : DifferentiableAt ℂ (fun t => f t j) (Function.update w i (w i)) := by
    rw [Function.update_eq_self]
    exact (hj w hw).differentiableAt (hU.mem_nhds hw)
  exact hw.comp (w i) (hasFDerivAt_update w (w i)).differentiableAt

noncomputable def jac {k : ℕ} (g : (Fin k → ℂ) → Fin k → ℂ) (v : Fin k → ℂ) : ℂ :=
  LinearMap.det (fderiv ℂ g v : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)

theorem jac_ne_zero_iff {k : ℕ} (g : (Fin k → ℂ) → Fin k → ℂ) (v : Fin k → ℂ) :
    jac g v ≠ 0 ↔ Function.Injective (fderiv ℂ g v) := by
  rw [jac, ← isUnit_iff_ne_zero, ← LinearMap.isUnit_iff_isUnit_det, Module.End.isUnit_iff]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, LinearMap.injective_iff_surjective.1 h⟩

theorem differentiableOn_jac {k : ℕ} {Ω : Set (Fin k → ℂ)} {g : (Fin k → ℂ) → Fin k → ℂ} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) : DifferentiableOn ℂ (jac g) Ω := by
  have hfd : DifferentiableOn ℂ (fderiv ℂ g) Ω :=
    (analyticOnNhd_of_differentiableOn hΩ hg).fderiv.differentiableOn
  have hentry : ∀ i j : Fin k,
      DifferentiableOn ℂ (fun v => fderiv ℂ g v (Pi.single j 1) i) Ω := fun i j =>
    differentiableOn_pi.1 (hfd.clm_apply (differentiableOn_const _)) i
  have hjac : jac g = fun v => ∑ σ : Equiv.Perm (Fin k),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, fderiv ℂ g v (Pi.single i 1) (σ i) := by
    funext v
    rw [jac, ← LinearMap.det_toMatrix', Matrix.det_apply']
    simp [LinearMap.toMatrix'_apply]
  rw [hjac]
  refine DifferentiableOn.fun_sum fun σ _ => (differentiableOn_const _).mul ?_
  intro x hx
  exact (HasFDerivWithinAt.finsetProd (u := Finset.univ)
    (g := fun i v => fderiv ℂ g v (Pi.single i 1) (σ i))
    fun i _ => ((hentry (σ i) i) x hx).hasFDerivWithinAt).differentiableWithinAt

theorem proof (hFin : CompactHolomorphicFibreFinite.Statement) (hInf : RankDeficientFibreInfinite.Statement)
    (hDim : HolomorphicZeroSetDimH.Statement) (hConn : HausdorffNullComplementConnected.Statement) :
    ProperHolomorphicSurjective.Statement := by
  intro k Ω D g hΩ hΩne hD hDc hg hmaps hprop
  refine Set.Subset.antisymm (Set.image_subset_iff.2 hmaps) ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · intro y _
    obtain ⟨v, hv⟩ := hΩne
    exact ⟨v, hv, Subsingleton.elim _ _⟩
  have han := analyticOnNhd_of_differentiableOn hΩ hg
  have hfr : Module.finrank ℝ (Fin k → ℂ) = 2 * k := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]

  have hopen : ∀ v ∈ Ω, jac g v ≠ 0 → g '' Ω ∈ 𝓝 (g v) := by
    intro v hv hdet
    have he : ((LinearMap.equivOfDetNeZero (fderiv ℂ g v : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)
        hdet).toContinuousLinearEquiv : (Fin k → ℂ) →L[ℂ] Fin k → ℂ) = fderiv ℂ g v := by
      ext1 u
      rfl
    have hs : HasStrictFDerivAt g ((LinearMap.equivOfDetNeZero
        (fderiv ℂ g v : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) hdet).toContinuousLinearEquiv :
          (Fin k → ℂ) →L[ℂ] Fin k → ℂ) v := by
      rw [he]
      exact (han v hv).hasStrictFDerivAt
    rw [← hs.map_nhds_eq_of_equiv]
    exact Filter.image_mem_map (hΩ.mem_nhds hv)

  have hreg : ∀ W ⊆ Ω, IsOpen W → W.Nonempty → ∃ w ∈ W, jac g w ≠ 0 := by
    intro W hW hWo hWne
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    obtain ⟨y, hy⟩ := hInf k k W g hWo hWne (hg.mono hW)
      fun v hv hinj => (jac_ne_zero_iff g v).2 hinj (hcon v hv)
    obtain ⟨t, htW, hty⟩ := hy.nonempty
    have hyD : y ∈ D := hty ▸ hmaps (hW htW)
    have hcpt : IsCompact {v | v ∈ Ω ∧ g v = y} :=
      hprop {y} (Set.singleton_subset_iff.2 hyD) isCompact_singleton
    exact hy ((hFin k k Ω g y hΩ hg hcpt).subset fun t ht => ⟨hW ht.1, ht.2⟩)

  set C : Set (Fin k → ℂ) := g '' {v | v ∈ Ω ∧ jac g v = 0} with hC
  have hdimC : dimH C ≤ 2 * ((k - 1 : ℕ) : ℝ≥0∞) := by
    refine le_trans ?_ (hDim k Ω (jac g) hΩ (differentiableOn_jac hΩ hg) hreg)
    refine dimH_image_le_of_locally_lipschitzOn fun x hx => ?_
    obtain ⟨K, t, ht, hL⟩ := ((han x hx.1).contDiffAt (n := 1)).exists_lipschitzOnWith
    exact ⟨K, t, nhdsWithin_le_nhds ht, hL⟩
  have hnull : μH[(Module.finrank ℝ (Fin k → ℂ) : ℝ) - 1] C = 0 := by
    have hlt : dimH C < (((2 * k - 1 : ℕ) : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.coe_natCast]
      calc dimH C ≤ 2 * ((k - 1 : ℕ) : ℝ≥0∞) := hdimC
        _ = ((2 * (k - 1) : ℕ) : ℝ≥0∞) := by push_cast; ring
        _ < ((2 * k - 1 : ℕ) : ℝ≥0∞) := by exact_mod_cast (by omega : 2 * (k - 1) < 2 * k - 1)
    have h0 := hausdorffMeasure_of_dimH_lt hlt
    have hexp : ((((2 * k - 1 : ℕ) : ℝ≥0)) : ℝ) = (Module.finrank ℝ (Fin k → ℂ) : ℝ) - 1 := by
      rw [hfr, NNReal.coe_natCast, Nat.cast_sub (by omega)]
      push_cast
      ring
    rwa [hexp] at h0
  have hR : IsPreconnected (D \ C) := hConn (Fin k → ℂ) D C hD hDc hnull

  have hclosed : ∀ y ∈ D, y ∈ closure (g '' Ω) → y ∈ g '' Ω := by
    intro y hyD hycl
    obtain ⟨r, hr, hrD⟩ := Metric.isOpen_iff.1 hD y hyD
    have hLD : closedBall y (r / 2) ⊆ D := (closedBall_subset_ball (by linarith)).trans hrD
    have hK := hprop (closedBall y (r / 2)) hLD (isCompact_closedBall y (r / 2))
    have hgK : IsCompact (g '' (Ω ∩ g ⁻¹' closedBall y (r / 2))) :=
      hK.image_of_continuousOn (hg.continuousOn.mono Set.inter_subset_left)
    refine Set.image_mono Set.inter_subset_left (hgK.isClosed.closure_subset ?_)
    rw [mem_closure_iff_nhds] at hycl ⊢
    intro U hU
    obtain ⟨z, ⟨hzU, hzB⟩, v, hv, rfl⟩ :=
      hycl (U ∩ ball y (r / 2)) (Filter.inter_mem hU (ball_mem_nhds y (by linarith)))
    exact ⟨g v, hzU, v, ⟨hv, ball_subset_closedBall hzB⟩, rfl⟩

  have hne : ((D \ C) ∩ interior (g '' Ω)).Nonempty := by
    obtain ⟨w, hwΩ, hw⟩ := hreg Ω subset_rfl hΩ hΩne
    have hN : g '' Ω ∈ 𝓝 (g w) := hopen w hwΩ hw
    by_contra hcon
    have hsubC : interior (g '' Ω) ⊆ C := by
      intro z hz
      by_contra hzC
      exact hcon ⟨z, ⟨Set.image_subset_iff.2 hmaps (interior_subset hz), hzC⟩, hz⟩
    have h1 : dimH (interior (g '' Ω)) = Module.finrank ℝ (Fin k → ℂ) :=
      Real.dimH_of_nonempty_interior (by rw [interior_interior]; exact ⟨g w, mem_interior_iff_mem_nhds.2 hN⟩)
    have h2 := (dimH_mono hsubC).trans hdimC
    rw [h1, hfr, show (2 : ℝ≥0∞) * ((k - 1 : ℕ) : ℝ≥0∞) = ((2 * (k - 1) : ℕ) : ℝ≥0∞) by push_cast; ring]
      at h2
    have h3 : 2 * k ≤ 2 * (k - 1) := by exact_mod_cast h2
    omega

  have hRsub : D \ C ⊆ interior (g '' Ω) ∪ (closure (g '' Ω))ᶜ := by
    rintro y ⟨hyD, hyC⟩
    by_cases hyE : y ∈ g '' Ω
    · left
      obtain ⟨v, hv, rfl⟩ := hyE
      have hjv : jac g v ≠ 0 := fun h0 => hyC ⟨v, ⟨hv, h0⟩, rfl⟩
      exact mem_interior_iff_mem_nhds.2 (hopen v hv hjv)
    · right
      exact fun hcl => hyE (hclosed y hyD hcl)
  have hdisj : Disjoint (interior (g '' Ω)) (closure (g '' Ω))ᶜ :=
    Set.disjoint_compl_right_iff_subset.2 (interior_subset.trans subset_closure)
  have hRE := hR.subset_left_of_subset_union isOpen_interior isClosed_closure.isOpen_compl hdisj hRsub hne
  intro y hyD
  by_cases hyC : y ∈ C
  · obtain ⟨v, ⟨hv, _⟩, rfl⟩ := hyC
    exact ⟨v, hv, rfl⟩
  · exact interior_subset (hRE ⟨hyD, hyC⟩)

end ProperHolomorphicSurjective

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Topology Metric

noncomputable section

namespace ImplicitCurve

theorem analyticOnNhd_of_differentiableOn {m p : ℕ} {U : Set (Fin m → ℂ)}
    {Φ : (Fin m → ℂ) → Fin p → ℂ} (hU : IsOpen U) (hΦ : DifferentiableOn ℂ Φ U) :
    AnalyticOnNhd ℂ Φ U := by
  refine analyticOnNhd_pi_iff.2 fun j => ?_
  have hj : DifferentiableOn ℂ (fun t => Φ t j) U := differentiableOn_pi.1 hΦ j
  refine IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hU hj.continuousOn
    fun w hw i => ?_
  have hw : DifferentiableAt ℂ (fun t => Φ t j) (Function.update w i (w i)) := by
    rw [Function.update_eq_self]; exact (hj w hw).differentiableAt (hU.mem_nhds hw)
  exact hw.comp (w i) (hasFDerivAt_update w (w i)).differentiableAt

theorem proof : ImplicitCurve.Statement := by
  intro n k γ R L s hγ hs hbij
  set F : (Fin (k + 1) → ℂ) → Fin (k + 1) → ℂ := fun t => vecCons (t 0) (L *ᵥ γ t) with hF
  have hFd : DifferentiableOn ℂ F (ball 0 R) := by
    refine differentiableOn_pi.2 fun i => Fin.cases ?_ (fun j => ?_) i
    · simpa [hF] using (differentiableOn_pi.1 (differentiableOn_id (s := ball (0 : Fin (k + 1) → ℂ) R)) 0)
    · simp only [hF, cons_val_succ, mulVec, dotProduct]
      exact DifferentiableOn.fun_sum fun l _ => (differentiableOn_pi.1 hγ l).const_mul _
  have hFa := analyticOnNhd_of_differentiableOn isOpen_ball hFd
  set e := (LinearEquiv.ofBijective
    (fderiv ℂ F s : (Fin (k + 1) → ℂ) →ₗ[ℂ] Fin (k + 1) → ℂ) hbij).toContinuousLinearEquiv
  have he : (e : (Fin (k + 1) → ℂ) →L[ℂ] Fin (k + 1) → ℂ) = fderiv ℂ F s := by ext1 x; rfl
  have hst : HasStrictFDerivAt F (e : (Fin (k + 1) → ℂ) →L[ℂ] Fin (k + 1) → ℂ) s := by
    rw [he]; exact (hFa s hs).hasStrictFDerivAt
  have hV : ∀ᶠ t in 𝓝 s, (t ∈ ball (0 : Fin (k + 1) → ℂ) R ∧ fderiv ℂ F t ∈
      Set.range ((↑) : ((Fin (k + 1) → ℂ) ≃L[ℂ] (Fin (k + 1) → ℂ)) → _)) ∧
      t ∈ (hst.toOpenPartialHomeomorph F).source :=
    (Filter.Eventually.and (isOpen_ball.mem_nhds hs) ((hFa s hs).fderiv.continuousAt.preimage_mem_nhds
      (ContinuousLinearEquiv.isOpen.mem_nhds ⟨e, he⟩))).and
      ((hst.toOpenPartialHomeomorph F).open_source.mem_nhds hst.mem_toOpenPartialHomeomorph_source)
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV
  set Ψ := (hst.toOpenPartialHomeomorph F).restrOpen (ball s ε) isOpen_ball
  have hΨs : Ψ.source = (hst.toOpenPartialHomeomorph F).source ∩ ball s ε :=
    OpenPartialHomeomorph.restrOpen_source _ _ _
  have hsΨ : s ∈ Ψ.source := hΨs ▸ ⟨hst.mem_toOpenPartialHomeomorph_source, mem_ball_self hε⟩
  have hsrc : ∀ t ∈ Ψ.source, t ∈ ball 0 R ∧
      ∃ e' : (Fin (k + 1) → ℂ) ≃L[ℂ] (Fin (k + 1) → ℂ), HasFDerivAt Ψ (e' : _ →L[ℂ] _) t := by
    intro t ht
    obtain ⟨⟨htR, e', he'⟩, -⟩ := hεV (hΨs ▸ ht).2
    refine ⟨htR, e', ?_⟩
    rw [he']; exact (hFa t htR).differentiableAt.hasFDerivAt
  obtain ⟨r, hr, hrT⟩ := Metric.isOpen_iff.1 Ψ.open_target (F s) (Ψ.map_source hsΨ)
  set p : (Fin 1 → ℂ) → Fin (k + 1) → ℂ := fun τ => vecCons (s 0 + τ 0) (L *ᵥ γ s) with hp
  have hpT : ∀ τ ∈ ball (0 : Fin 1 → ℂ) r, p τ ∈ Ψ.target := by
    intro τ hτ
    refine hrT ((dist_pi_lt_iff hr).2 fun i => Fin.cases ?_ (fun j => ?_) i)
    · simpa [hp, hF, dist_eq_norm] using (norm_le_pi_norm τ 0).trans_lt (mem_ball_zero_iff.1 hτ)
    · simpa [hp, hF] using hr
  refine ⟨r, hr, fun τ => Ψ.symm (p τ), fun τ hτ => ?_, ?_, fun τ hτ => ?_, ?_⟩
  · have hpd : Differentiable ℂ p := differentiable_pi.2 fun i => Fin.cases
      (by simpa [hp] using (differentiable_const (s 0)).add (differentiable_pi.1 differentiable_id 0))
      (fun j => by simp [hp]) i
    obtain ⟨-, e', he'⟩ := hsrc _ (Ψ.map_target (hpT τ hτ))
    exact ((Ψ.hasFDerivAt_symm (hpT τ hτ) he').differentiableAt.comp τ
      (hpd τ)).differentiableWithinAt
  · have h0 : p 0 = F s := by simp [hp, hF]
    show Ψ.symm (p 0) = s
    rw [h0]; exact Ψ.left_inv hsΨ
  · have h2 : F (Ψ.symm (p τ)) = p τ := Ψ.right_inv (hpT τ hτ)
    refine ⟨(hsrc _ (Ψ.map_target (hpT τ hτ))).1, ?_, ?_⟩
    · simpa [hF, hp] using congrFun h2 0
    · simpa [hF, hp] using congrArg Fin.tail h2
  · refine ⟨Ψ.source ∩ {t | ‖t 0 - s 0‖ < r}, Filter.inter_mem (Ψ.open_source.mem_nhds hsΨ)
      ((isOpen_lt ((continuous_apply 0).sub continuous_const).norm continuous_const).mem_nhds
        (by simpa using hr)), ?_⟩
    rintro t ⟨ht, htr⟩ hL
    refine ⟨fun _ => t 0 - s 0, by simpa [pi_norm_const] using htr, ?_⟩
    have hpt : p (fun _ => t 0 - s 0) = F t := by simp [hp, hF, hL]
    dsimp only
    rw [hpt]; exact Ψ.left_inv ht

end ImplicitCurve

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Module

noncomputable section

namespace SheetImageAreaSet

theorem exists_adapted_frame {n d : ℕ}
    (P : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin d)) (hP : Function.Surjective P) :
    ∃ (m : ℕ) (e : Fin n ≃ Fin d ⊕ Fin m)
      (Q : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))
      (L : EuclideanSpace ℂ (Fin d) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin d))
      (π : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)),
      (∀ z, ‖Q z‖ = ‖z‖) ∧
        ∀ z, Q z = WithLp.toLp 2 (fun j => Sum.elim (fun i => L (P z) i) (fun i => π z i) (e j)) := by
  classical
  set K := LinearMap.ker P with hKdef
  have h1 := K.finrank_add_finrank_orthogonal
  have h2 := LinearMap.finrank_range_add_finrank_ker P
  rw [LinearMap.range_eq_top.2 hP, finrank_top] at h2
  simp only [finrank_euclideanSpace_fin] at h1 h2
  rw [← hKdef] at h2
  have hW : finrank ℂ Kᗮ = d := by omega
  have hn : n = d + finrank ℂ K := by omega
  let bW : OrthonormalBasis (Fin d) ℂ Kᗮ := (stdOrthonormalBasis ℂ Kᗮ).reindex (finCongr hW)
  let bK := stdOrthonormalBasis ℂ K
  let e : Fin n ≃ Fin d ⊕ Fin (finrank ℂ K) := (finCongr hn).trans finSumFinEquiv.symm
  let πW : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin d) :=
    bW.repr.toLinearMap ∘ₗ (Kᗮ.orthogonalProjectionOnto : _ →L[ℂ] Kᗮ).toLinearMap
  let π : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin (finrank ℂ K)) :=
    bK.repr.toLinearMap ∘ₗ (K.orthogonalProjectionOnto : _ →L[ℂ] K).toLinearMap
  obtain ⟨R, hR⟩ := P.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hP)
  have hPR : ∀ y, P (R y) = y := fun y => LinearMap.congr_fun hR y
  have hWR : ∀ z, πW (R (P z)) = πW z := by
    intro z
    have hmem : R (P z) - z ∈ Kᗮᗮ :=
      K.le_orthogonal_orthogonal (by simp [hKdef, LinearMap.mem_ker, hPR])
    have h0 := Submodule.orthogonalProjectionOnto_eq_zero_iff.2 hmem
    have h3 : πW (R (P z) - z) = 0 := by simp [πW, h0]
    rwa [map_sub, sub_eq_zero] at h3
  have hinj : Function.Injective (πW ∘ₗ R) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h0 : Kᗮ.orthogonalProjectionOnto (R y) = 0 := by simpa [πW] using hy
    rw [Submodule.orthogonalProjectionOnto_eq_zero_iff, K.orthogonal_orthogonal] at h0
    rw [← hPR y]
    exact h0
  let L := LinearEquiv.ofInjectiveEndo _ hinj
  let Q : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    { toFun := fun z => WithLp.toLp 2 (fun j => Sum.elim (fun i => πW z i) (fun i => π z i) (e j))
      map_add' := fun z w => by
        ext j
        obtain ⟨s, rfl⟩ := e.symm.surjective j
        rcases s with i | i <;> simp
      map_smul' := fun c z => by
        ext j
        obtain ⟨s, rfl⟩ := e.symm.surjective j
        rcases s with i | i <;> simp }
  refine ⟨finrank ℂ K, e, Q, L, π, fun z => ?_, fun z => ?_⟩
  · refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    show ‖(WithLp.toLp 2 (fun j => Sum.elim (fun i => πW z i) (fun i => π z i) (e j)) :
      EuclideanSpace ℂ (Fin n))‖ ^ 2 = _
    rw [GraphAreaHolomorphic.norm_sq_sumElim e (πW z) (π z), Submodule.norm_sq_eq_add_norm_sq_projection z K,
      add_comm]
    simp [πW, π]
  · show WithLp.toLp 2 (fun j => Sum.elim (fun i => πW z i) (fun i => π z i) (e j)) = _
    simp [L, hWR]

theorem areaJacobian_eq_normDet {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (M : E →ₗ[ℝ] F) : areaJacobian M = M.normDet := by
  have h := M.normDet_sq
  simp only [RCLike.ofReal_real_eq_id, id_eq] at h
  rw [areaJacobian, ← h, Real.sqrt_sq M.normDet_nonneg]

theorem areaJacobian_comp_of_norm {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (Q : F →ₗ[ℝ] F) (hQ : ∀ v, ‖Q v‖ = ‖v‖) (M : E →ₗ[ℝ] F) :
    areaJacobian (Q ∘ₗ M) = areaJacobian M := by
  rw [areaJacobian_eq_normDet, areaJacobian_eq_normDet, LinearMap.normDet_comp,
    show (Q.domRestrict (LinearMap.range M)).normDet = 1 from
      LinearIsometry.normDet_eq_one ⟨Q.domRestrict _, fun v => hQ v⟩, one_mul]

theorem areaJacobian_comp_endo {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (M : E →ₗ[ℝ] F) (T : E →ₗ[ℝ] E) :
    areaJacobian (M ∘ₗ T) = areaJacobian M * |LinearMap.det T| := by
  rw [areaJacobian_eq_normDet, areaJacobian_eq_normDet, LinearMap.normDet_comp_of_finrank_eq _ _ rfl,
    LinearMap.normDet_eq_abs_det]

end SheetImageAreaSet

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

theorem SliceUnmixedGeneral.proof (hA : CMHeightOneGeneral.Statement) (hC : LocalDimDomain.Statement)
    (hB : SliceLocalDimGeneral.Statement) (hD : SliceCMUnmixed.Statement) :
    SliceUnmixedGeneral.Statement := by
  intro n d J W u hJ hdim hu hW
  obtain ⟨f, hfW, hf⟩ := hA n J W (linForm u) hJ hu hW
  refine ⟨f, hfW, fun q hq hfq => ?_⟩
  have hqJ : q ∈ zeroSet J := fun g hg => hq g (hW.1.2 (Ideal.mem_sup_left hg))
  obtain ⟨O, hOo, hOd, hO⟩ := hB n d J q hJ hdim hqJ
  exact ⟨O, hOo, hOd, fun L hL =>
    hD n d J L q (hf q hq hfq) (hC n (d + 1) J hJ hdim q hqJ) (hO L hL)⟩

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

theorem NormalModelDivisorChartGeneric.proof (h₁ : NormalModelGoodPointGeneric.Statement)
    (h₂ : NormalModelGoodPointChart.Statement) : NormalModelDivisorChartGeneric.Statement := by
  intro n d J u M hJ hd hu
  obtain ⟨B, hB, hBd, hgood⟩ := h₁ n d J u M hJ hd hu
  exact ⟨B, hB, hBd, fun w hw hu0 hwB => h₂ n d J u M w (hgood w hw hu0 hwB)⟩

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def CentredIntegralEquation.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (p : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    (∀ i, AnalyticAt ℂ (p i) w) →
    (∀ i : σ, ∃ (n : ℕ) (b : Fin n → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (b j) (A w)) ∧
      IsGermCombination w p (fun z => z i ^ n + ∑ j, b j (A z) * z i ^ (j : ℕ))) →
    (∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g w →
      ∃ (s : Finset (σ → ℕ)) (a : (σ → ℕ) → (Fin d → ℂ) → ℂ), (∀ m ∈ s, AnalyticAt ℂ (a m) (A w)) ∧
        IsGermCombination w p (fun z => g z - ∑ m ∈ s, a m (A z) * ∏ i, z i ^ m i)) →
    ∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g w →
      ∃ (n : ℕ) (b : Fin n → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (b j) (A w)) ∧
        IsGermCombination w p (fun z => g z ^ n + ∑ j, b j (A z) * g z ^ (j : ℕ)) ∧
        ∀ T : ℂ, T ^ n + ∑ j, b j (A w) * T ^ (j : ℕ) = (T - g w) ^ n

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
