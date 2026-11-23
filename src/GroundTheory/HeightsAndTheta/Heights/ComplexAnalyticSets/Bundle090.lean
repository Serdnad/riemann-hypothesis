module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionAnalytic
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.HolomorphicZerosNotIsolated
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle072
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularLocusDense
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle073
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle089
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.Regular.ProjectiveDimension
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle003

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology

noncomputable section

theorem AnalyticRootBranch.proof : AnalyticRootBranch.Statement := by
  intro d N a t₀ τ₀ ha hsep hroot
  set p : Polynomial ℂ := Polynomial.X ^ N + ∑ j, Polynomial.C (a j t₀) * Polynomial.X ^ (j : ℕ) with hp
  set F : (Fin d → ℂ) × ℂ → ℂ := fun v => v.2 ^ N + ∑ j, a j v.1 * v.2 ^ (j : ℕ) with hF
  have hFa : AnalyticAt ℂ F (t₀, τ₀) := by
    refine (analyticAt_snd.pow N).add (Finset.analyticAt_fun_sum _ fun j _ => ?_)
    exact ((ha j).comp (analyticAt_fst (p := (t₀, τ₀)))).mul (analyticAt_snd.pow _)
  have hcd : ContDiffAt ℂ 1 F (t₀, τ₀) := hFa.contDiffAt

  have hpe : ∀ s, p.eval s = F (t₀, s) := by
    intro s
    simp [hp, hF, Polynomial.eval_finsetSum]

  have hpart : fderiv ℂ F (t₀, τ₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ =
      (1 : ℂ →L[ℂ] ℂ).smulRight (p.derivative.eval τ₀) := by
    have h1 : HasFDerivAt (fun s : ℂ => F (t₀, s))
        (fderiv ℂ F (t₀, τ₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ) τ₀ :=
      (hFa.differentiableAt.hasFDerivAt).comp τ₀
        ((hasFDerivAt_const t₀ τ₀).prodMk (hasFDerivAt_id τ₀))
    have h2 : (fun s : ℂ => F (t₀, s)) = fun s => p.eval s := funext fun s => (hpe s).symm
    rw [h2] at h1
    exact h1.unique (p.hasDerivAt τ₀).hasFDerivAt

  have hder : p.derivative.eval τ₀ ≠ 0 := by
    have h := hsep.eval₂_derivative_ne_zero (RingHom.id ℂ) (x := τ₀)
      (by rw [Polynomial.eval₂_id, hpe]; exact hroot)
    rwa [Polynomial.eval₂_id] at h
  have hinv : (fderiv ℂ F (t₀, τ₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
    rw [hpart]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ hder), ?_⟩
    ext; simp
  set ψ := hcd.implicitFunction one_ne_zero hinv with hψdef
  have hψt : ψ t₀ = τ₀ := hcd.implicitFunction_apply_self one_ne_zero hinv
  have hψcd : ContDiffAt ℂ 1 ψ t₀ := hcd.contDiffAt_implicitFunction one_ne_zero hinv
  obtain ⟨O, hOsub, hOo, ht₀O⟩ := eventually_nhds_iff.mp
    ((hcd.eventually_apply_implicitFunction one_ne_zero hinv).and (hψcd.eventually (by simp)))
  refine ⟨O, ψ, hOo, ht₀O, ?_, hψt, fun t ht => (hOsub t ht).1.trans hroot⟩
  refine RiemannExtensionAnalytic.analyticOnNhd_of_differentiableOn hOo fun t ht => ?_
  exact ((hOsub t ht).2.differentiableAt one_ne_zero).differentiableWithinAt

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology

theorem HolomorphicKernelFibre.proof : HolomorphicKernelFibre.Statement := by
  intro k U f b hU hf hb d hd
  set A : (Fin k → ℂ) →L[ℂ] Fin k → ℂ := fderiv ℂ f b with hA
  have hfa : AnalyticAt ℂ f b := InjectiveHolomorphicInverse.analyticAt_of_differentiableOn hU hf hb
  have hfd : HasFDerivAt f A b := (hf.differentiableAt (hU.mem_nhds hb)).hasFDerivAt
  set W := LinearMap.range (A : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) with hW
  set K := LinearMap.ker (A : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) with hK
  obtain ⟨C, hWC⟩ := W.exists_isCompl
  obtain ⟨K', hKK'⟩ := K.exists_isCompl
  have hdimC : Module.finrank ℂ C = Module.finrank ℂ (Fin d → ℂ) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (A : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)
    have h2 := Submodule.finrank_add_eq_of_isCompl hWC
    rw [Module.finrank_fin_fun]
    rw [← hW, ← hK, hd] at h1
    omega
  have hdimK : Module.finrank ℂ K = Module.finrank ℂ (Fin d → ℂ) := by
    rw [Module.finrank_fin_fun]; exact hd
  let eC : C ≃ₗ[ℂ] (Fin d → ℂ) := LinearEquiv.ofFinrankEq _ _ hdimC
  let eK : K ≃ₗ[ℂ] (Fin d → ℂ) := LinearEquiv.ofFinrankEq _ _ hdimK
  let P : (Fin k → ℂ) →L[ℂ] Fin k → ℂ := LinearMap.toContinuousLinearMap (W.projection C hWC)
  let E : (Fin d → ℂ) →L[ℂ] Fin k → ℂ :=
    LinearMap.toContinuousLinearMap (C.subtype ∘ₗ (eC.symm : (Fin d → ℂ) →ₗ[ℂ] C))
  let lam : (Fin k → ℂ) →L[ℂ] Fin d → ℂ :=
    LinearMap.toContinuousLinearMap ((eK : K →ₗ[ℂ] Fin d → ℂ) ∘ₗ K.projectionOnto K' hKK')
  let ℓ : (Fin k → ℂ) →L[ℂ] Fin d → ℂ :=
    LinearMap.toContinuousLinearMap ((eC : C →ₗ[ℂ] Fin d → ℂ) ∘ₗ C.projectionOnto W hWC.symm)
  have hEC : ∀ t, E t ∈ C := fun t => (eC.symm t).2
  have hEinj : Function.Injective E := fun s t hst => by
    have : eC.symm s = eC.symm t := Subtype.ext hst
    exact eC.symm.injective this
  have hPE : ∀ t, P (E t) = 0 := fun t => Submodule.projection_apply_of_mem_right hWC (hEC t)
  have hPP : ∀ x, P (P x) = P x := fun x =>
    Submodule.projection_apply_of_mem_left hWC (Submodule.projection_apply_mem hWC x)
  have hPA : ∀ v, P (A v) = A v := fun v =>
    Submodule.projection_apply_of_mem_left hWC (LinearMap.mem_range_self _ v)
  have hℓA : ∀ v, ℓ (A v) = 0 := fun v => by
    have h0 : C.projectionOnto W hWC.symm (A v) = 0 :=
      Submodule.projectionOnto_apply_of_mem_right hWC.symm (LinearMap.mem_range_self _ v)
    show eC (C.projectionOnto W hWC.symm (A v)) = 0
    rw [h0, map_zero]

  let M : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ := (A : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) + (E.comp lam : _)
  have hMinj : Function.Injective M := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    have hv' : A v + E (lam v) = 0 := hv
    have hAv : A v = 0 := by
      refine (Submodule.disjoint_def.mp hWC.disjoint) (A v) (LinearMap.mem_range_self _ v) ?_
      rw [eq_neg_of_add_eq_zero_left hv']
      exact C.neg_mem (hEC _)
    have hlv : lam v = 0 := by
      rw [hAv, zero_add] at hv'
      exact hEinj (hv'.trans (map_zero E).symm)
    have hvK : v ∈ K := hAv
    have : eK (K.projectionOnto K' hKK' v) = 0 := hlv
    rw [Submodule.projectionOnto_apply_of_mem_left hKK' hvK, LinearEquiv.map_eq_zero_iff] at this
    exact congrArg Subtype.val this
  let M' : (Fin k → ℂ) ≃L[ℂ] Fin k → ℂ := (LinearEquiv.ofInjectiveEndo M hMinj).toContinuousLinearEquiv
  let Φ : (Fin k → ℂ) → Fin k → ℂ := fun z => P (f z) + E (lam z)
  have hΦd : HasFDerivAt Φ (M' : (Fin k → ℂ) →L[ℂ] Fin k → ℂ) b := by
    have h := (P.hasFDerivAt.comp b hfd).add (E.comp lam).hasFDerivAt
    have hM : P.comp A + E.comp lam = (M' : (Fin k → ℂ) →L[ℂ] Fin k → ℂ) := by
      ext1 v
      show P (A v) + E (lam v) = A v + E (lam v)
      rw [hPA]
    rw [hM] at h
    exact h
  have hΦc : ContDiffAt ℂ 1 Φ b :=
    (P.contDiff.contDiffAt.comp b hfa.contDiffAt).add (E.comp lam).contDiff.contDiffAt
  let H := hΦc.toOpenPartialHomeomorph Φ hΦd one_ne_zero
  have hHΦ : ∀ z, H z = Φ z := fun z => rfl
  have hbS : b ∈ H.source := hΦc.mem_toOpenPartialHomeomorph_source hΦd one_ne_zero
  have hΦbT : Φ b ∈ H.target := hΦc.image_mem_toOpenPartialHomeomorph_target hΦd one_ne_zero
  have hinv : ContDiffAt ℂ 1 H.symm (Φ b) := hΦc.to_localInverse hΦd one_ne_zero
  have hHb : H.symm (Φ b) = b := by rw [← hHΦ]; exact H.left_inv hbS
  obtain ⟨O, hO, hOo, hbO⟩ := eventually_nhds_iff.mp (hinv.eventually (by simp))
  set c := P (f b) with hc
  let T := (H.target ∩ H.symm ⁻¹' U) ∩ O
  have hTo : IsOpen T := (H.isOpen_inter_preimage_symm hU).inter hOo
  let aff : (Fin d → ℂ) → Fin k → ℂ := fun t => c + E t
  have haff : Continuous aff := continuous_const.add E.continuous
  refine ⟨aff ⁻¹' T, lam b, fun t => H.symm (aff t), ℓ, hTo.preimage haff, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show c + E (lam b) ∈ T
    refine ⟨⟨hΦbT, ?_⟩, hbO⟩
    show H.symm (Φ b) ∈ U
    rw [hHb]; exact hb
  · intro t ht
    exact ((hO _ ht.2).differentiableAt one_ne_zero).comp t
      ((differentiableAt_const c).add E.differentiableAt) |>.differentiableWithinAt
  · intro t ht
    exact ht.1.2
  · intro s hs t ht hst
    have h1 := H.right_inv hs.1.1
    have h2 := H.right_inv ht.1.1
    have : aff s = aff t := by rw [← h1, ← h2]; exact congrArg H hst
    exact hEinj (add_left_cancel this)
  ·
    have hfib : ∀ t ∈ aff ⁻¹' T, P (f (H.symm (aff t))) = c := by
      intro t ht
      have h1 : Φ (H.symm (aff t)) = c + E t := H.right_inv ht.1.1
      have h2 := congrArg P h1
      simp only [Φ, map_add (f := _), hPE, add_zero, hPP] at h2
      rw [h2, hc, hPP]
    intro s hs t ht hst
    have hq : C.projectionOnto W hWC.symm (f (H.symm (aff s))) =
        C.projectionOnto W hWC.symm (f (H.symm (aff t))) := eC.injective hst
    rw [← Submodule.projection_add_projection_eq_self hWC (f (H.symm (aff s))),
      ← Submodule.projection_add_projection_eq_self hWC (f (H.symm (aff t)))]
    have hs' := hfib s hs
    have ht' := hfib t ht
    simp only [P, LinearMap.coe_toContinuousLinearMap'] at hs' ht'
    rw [hs', ht', Submodule.projection_apply, Submodule.projection_apply (q := W), hq]
  ·
    have hγy : H.symm (aff (lam b)) = b := hHb
    have hγd : DifferentiableAt ℂ (fun t => H.symm (aff t)) (lam b) :=
      (hinv.differentiableAt one_ne_zero).comp (lam b) ((differentiableAt_const c).add E.differentiableAt)
    have hfd' : HasFDerivAt f A (H.symm (aff (lam b))) := by rw [hγy]; exact hfd
    have h := ℓ.hasFDerivAt.comp (lam b) (hfd'.comp (lam b) hγd.hasFDerivAt)
    refine h.fderiv.trans ?_
    ext1 v
    exact hℓA _

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric

theorem CriticalFlatNotInjective.proof : CriticalFlatNotInjective.Statement := by
  intro k U f a hk hU hf haU hJa hflat hinj
  set J : (Fin k → ℂ) → ℂ := fun z => LinearMap.det (fderiv ℂ f z : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) with hJdef
  have hJan : AnalyticOnNhd ℂ J U := fun z hz =>
    analyticAt_det_fderiv (InjectiveHolomorphicInverse.analyticAt_of_differentiableOn hU hf hz)
  set Z : Set (Fin k → ℂ) := {z | J z = 0} with hZdef
  have hZ : IsAnalyticNear Z a := by
    refine ⟨U, 1, fun _ => J, hU, haU, fun _ => hJan, ?_⟩
    ext z
    simp only [hZdef, Set.mem_inter_iff, Set.mem_ofPred_eq, forall_const]
    tauto
  obtain ⟨N, hN, haN, hdense⟩ :=
    RegularLocusDense.proof AnalyticImplicitChart.proof (Fin k) Z a hZ
  have hB : IsOpen (N ∩ U) := hN.inter hU
  have ha : a ∈ closure (regLocus (Z ∩ (N ∩ U))) :=
    hdense (N ∩ U) hB Set.inter_subset_left ⟨hJa, haN, haU⟩
  obtain ⟨c, hc⟩ : (regLocus (Z ∩ (N ∩ U))).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at ha
    exact ha
  obtain ⟨⟨hcZ, hcB⟩, d, A, O, V, g, hO, hV, hcV, hg, hAg, hYV⟩ := hc
  obtain ⟨y0, hy0O, hgy0⟩ : c ∈ g '' O := hYV ▸ ⟨⟨hcZ, hcB⟩, hcV⟩

  have hgO : ∀ y ∈ O, J (g y) = 0 ∧ g y ∈ U := by
    intro y hy
    have h1 : g y ∈ Z ∩ (N ∩ U) ∩ V := hYV ▸ Set.mem_image_of_mem g hy
    exact ⟨h1.1.1, h1.1.2.2⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd
  ·
    obtain ⟨z, ⟨hzV, hzB⟩, hzc, hz0⟩ := exists_zero_ne_near hk (hJan c hcB.2) hcZ
      (Filter.inter_mem (hV.mem_nhds hcV) (hB.mem_nhds hcB))
    obtain ⟨y1, -, hgy1⟩ : z ∈ g '' O := hYV ▸ ⟨⟨hz0, hzB⟩, hzV⟩
    exact hzc (by rw [← hgy1, ← hgy0, Subsingleton.elim y1 y0])
  ·
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO y0 hy0O
    have hconst : ∀ y ∈ ball y0 ε, f (g y) = f (g y0) := by
      intro y hy
      have hdiff : ∀ x ∈ ball y0 ε, DifferentiableAt ℂ (f ∘ g) x := fun x hx =>
        (hf.differentiableAt (hU.mem_nhds (hgO x (hball hx)).2)).comp x
          (hg x (hball hx)).differentiableAt
      refine (convex_ball y0 ε).is_const_of_fderivWithin_eq_zero (f := f ∘ g)
        (fun x hx => (hdiff x hx).differentiableWithinAt) (fun x hx => ?_) hy (mem_ball_self hε)
      rw [fderivWithin_of_isOpen isOpen_ball hx,
        fderiv_comp x (hf.differentiableAt (hU.mem_nhds (hgO x (hball hx)).2))
          (hg x (hball hx)).differentiableAt,
        hflat (g x) (hgO x (hball hx)).2 (hgO x (hball hx)).1, ContinuousLinearMap.zero_comp]
    set y1 : Fin d → ℂ := y0 + ((ε / 2 : ℝ) : ℂ) • (fun _ => (1 : ℂ)) with hy1
    have hy1ball : y1 ∈ ball y0 ε := by
      rw [mem_ball, dist_eq_norm, hy1, add_sub_cancel_left, norm_smul, pi_norm_const, norm_one, mul_one,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith
    have hy10 : y1 ≠ y0 := by
      intro h
      have h2 := congrFun (congrArg (· - y0) h) ⟨0, hd⟩
      simp only [hy1, add_sub_cancel_left, sub_self, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
        mul_one, Complex.ofReal_eq_zero] at h2
      linarith
    have heq : g y1 = g y0 :=
      hinj (hgO y1 (hball hy1ball)).2 (hgO y0 hy0O).2 (hconst y1 hy1ball)
    exact hy10 (by rw [← hAg y1 (hball hy1ball), ← hAg y0 hy0O, heq])

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter
open scoped ENNReal NNReal

noncomputable section

namespace HolomorphicZeroSetDimH

def partialDeriv {k : ℕ} (h : (Fin k → ℂ) → ℂ) (n : ℕ) (m : Fin n → Fin k) (v : Fin k → ℂ) : ℂ :=
  iteratedFDeriv ℂ n h v (fun j => Pi.basisFun ℂ (Fin k) (m j))

theorem dimH_le_of_local {X : Type*} [EMetricSpace X] [SecondCountableTopology X] {S : Set X}
    {c : ℝ≥0∞} (hS : ∀ x ∈ S, ∃ N ∈ 𝓝 x, dimH (S ∩ N) ≤ c) : dimH S ≤ c := by
  by_contra hlt
  obtain ⟨x, hx, hall⟩ := exists_mem_nhdsWithin_lt_dimH_of_lt_dimH (not_le.1 hlt)
  obtain ⟨N, hN, hc⟩ := hS x hx
  exact (not_le.2 (hall _ (inter_mem_nhdsWithin S hN))) hc

theorem dimH_image_le_of_analyticOnNhd {d : ℕ} {σ : Type*} [Fintype σ] {O : Set (Fin d → ℂ)}
    {g : (Fin d → ℂ) → σ → ℂ} (hg : AnalyticOnNhd ℂ g O) : dimH (g '' O) ≤ 2 * (d : ℝ≥0∞) := by
  refine (dimH_image_le_of_locally_lipschitzOn fun y hy => ?_).trans ?_
  · obtain ⟨K, t, ht, hK⟩ := ((hg y hy).contDiffAt (n := 1)).exists_lipschitzOnWith
    exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩
  · have hfin : Module.finrank ℝ (Fin d → ℂ) = 2 * d := by
      rw [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]
    calc dimH O ≤ dimH (Set.univ : Set (Fin d → ℂ)) := dimH_mono (Set.subset_univ _)
      _ = Module.finrank ℝ (Fin d → ℂ) := Real.dimH_univ_eq_finrank _
      _ = 2 * (d : ℝ≥0∞) := by rw [hfin]; push_cast; ring

theorem dimH_regular_zeros_le {k : ℕ} {U : Set (Fin k → ℂ)} {g : (Fin k → ℂ) → ℂ}
    (hg : AnalyticOnNhd ℂ g U) :
    dimH {v | v ∈ U ∧ g v = 0 ∧ fderiv ℂ g v ≠ 0} ≤ 2 * ((k - 1 : ℕ) : ℝ≥0∞) := by
  refine dimH_le_of_local fun p hp => ?_
  obtain ⟨d, A, O, V, φ, hd, hO, hV, hpV, -, hφ, -, hZ⟩ :=
    AnalyticImplicitChart.proof (Fin k) (Fin 1) (fun _ => g) p Set.univ (fun _ => hg p hp.1)
      (fun _ => hp.2.1) (linearIndependent_unique_iff.2 hp.2.2) univ_mem
  refine ⟨V, hV.mem_nhds hpV, ?_⟩
  have hk : k - 1 = d := by simp only [Fintype.card_fin] at hd; omega
  rw [hk]
  refine (dimH_mono ?_).trans (dimH_image_le_of_analyticOnNhd hφ)
  rw [← hZ]
  rintro z ⟨hz, hzV⟩
  exact ⟨hzV, fun _ => hz.2.1⟩

theorem exists_partialDeriv {k : ℕ} {U : Set (Fin k → ℂ)} {h : (Fin k → ℂ) → ℂ} (hU : IsOpen U)
    (hh : AnalyticOnNhd ℂ h U) (hW : ∀ W ⊆ U, IsOpen W → W.Nonempty → ∃ w ∈ W, h w ≠ 0)
    {v : Fin k → ℂ} (hv : v ∈ U) (h0 : h v = 0) :
    ∃ n m, partialDeriv h n m v = 0 ∧ fderiv ℂ (partialDeriv h n m) v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hdiff : ∀ n, DifferentiableAt ℂ (iteratedFDeriv ℂ n h) v := fun n =>
    ((hh.iteratedFDeriv n) v hv).differentiableAt
  have hall : ∀ n m, partialDeriv h n m v = 0 := by
    intro n
    induction n with
    | zero => intro m; simp [partialDeriv, iteratedFDeriv_zero_apply, h0]
    | succ n ih =>
      intro m
      have h1 := hcon n (Fin.tail m) (ih _)
      have h2 := congrArg (fun L => L (Pi.basisFun ℂ (Fin k) (m 0))) h1
      simp only [zero_apply] at h2
      unfold partialDeriv at h2 ⊢
      rw [fderiv_continuousMultilinear_apply_const_apply (hdiff n)] at h2
      rw [iteratedFDeriv_succ_apply_left]
      exact h2
  have hzero : ∀ n, iteratedFDeriv ℂ n h v = 0 := fun n =>
    ContinuousMultilinearMap.toMultilinearMap_injective
      (Module.Basis.ext_multilinear (fun _ => Pi.basisFun ℂ (Fin k)) fun m => by
        simpa [partialDeriv] using hall n m)
  obtain ⟨p, r, hp⟩ := hh v hv
  have hev : ∀ᶠ x in 𝓝 v, h x = 0 := by
    have h1 : Tendsto (fun x => x - v) (𝓝 v) (𝓝 0) := by
      simpa using (continuous_sub_right v).tendsto v
    filter_upwards [h1.eventually (Metric.eball_mem_nhds 0 hp.r_pos)] with x hx
    have hs := hp.hasSum_iteratedFDeriv hx
    simp only [hzero, zero_apply, smul_zero, add_sub_cancel] at hs
    exact hs.unique hasSum_zero
  obtain ⟨W, hWsub, hWo, hvW⟩ := _root_.mem_nhds_iff.1 (hev.and (hU.mem_nhds hv))
  obtain ⟨w, hw, hw0⟩ := hW W (fun x hx => (hWsub hx).2) hWo ⟨v, hvW⟩
  exact hw0 (hWsub hw).1

theorem proof : HolomorphicZeroSetDimH.Statement := by
  intro k U h hU hh hW
  have ha : AnalyticOnNhd ℂ h U :=
    analyticOnNhd_pi_iff.1 (ProperHolomorphicSurjective.analyticOnNhd_of_differentiableOn (m := 1)
      (f := fun v _ => h v) hU (differentiableOn_pi.2 fun _ => hh)) 0
  have hpd : ∀ n m, AnalyticOnNhd ℂ (partialDeriv h n m) U := fun n m x hx =>
    ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => Fin k → ℂ) ℂ
      (fun j => Pi.basisFun ℂ (Fin k) (m j))).analyticAt _).comp (ha.iteratedFDeriv n x hx)
  calc dimH {v | v ∈ U ∧ h v = 0}
      ≤ dimH (⋃ nm : (Σ n, Fin n → Fin k),
          {v | v ∈ U ∧ partialDeriv h nm.1 nm.2 v = 0 ∧ fderiv ℂ (partialDeriv h nm.1 nm.2) v ≠ 0}) := by
        refine dimH_mono fun v hv => ?_
        obtain ⟨n, m, h1, h2⟩ := exists_partialDeriv hU ha hW hv.1 hv.2
        exact Set.mem_iUnion.2 ⟨⟨n, m⟩, hv.1, h1, h2⟩
    _ ≤ 2 * ((k - 1 : ℕ) : ℝ≥0∞) := by
        rw [dimH_iUnion]
        exact iSup_le fun nm => dimH_regular_zeros_le (hpd nm.1 nm.2)

end HolomorphicZeroSetDimH

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing CategoryTheory RingTheory.Sequence

universe u

theorem hasProjectiveDimensionLE_sub_length_of_isWeaklyRegular (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (d : ℕ)
    (hd : ∀ rs : List R, (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs → rs.length ≤ d)
    (ms : List R) : ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] (n : ℕ),
      HasProjectiveDimensionLE (ModuleCat.of R M) n → (∀ r ∈ ms, r ∈ maximalIdeal R) →
        IsWeaklyRegular M ms → HasProjectiveDimensionLE (ModuleCat.of R M) (d - ms.length) := by
  induction ms with
  | nil =>
    intro M _ _ _ _ n hM _ _
    simpa using hasProjectiveDimensionLE_of_forall_isWeaklyRegular_length_le d R hd M n hM
  | cons x ms ih =>
    intro M _ _ _ _ n hM hms hreg
    simp only [List.mem_cons, forall_eq_or_imp] at hms
    rw [isWeaklyRegular_cons_iff] at hreg
    have : Nontrivial (QuotSMulTop x M) := nontrivial_quotSMulTop_of_mem_maximalIdeal M hms.1
    have heq : projectiveDimension (ModuleCat.of R (QuotSMulTop x M)) =
        projectiveDimension (ModuleCat.of R M) + 1 :=
      ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular (ModuleCat.of R M) x hreg.1 hms.1
    have hQ : HasProjectiveDimensionLE (ModuleCat.of R (QuotSMulTop x M)) (n + 1) := by
      rw [← projectiveDimension_le_iff, heq, Nat.cast_add, Nat.cast_one]
      gcongr
      exact (projectiveDimension_le_iff _ _).mpr hM
    have hih := ih (QuotSMulTop x M) (n + 1) hQ hms.2 hreg.2
    rw [← projectiveDimension_le_iff, heq] at hih
    rw [← projectiveDimension_le_iff, List.length_cons]
    rcases Nat.eq_zero_or_pos (d - ms.length) with h0 | hpos
    · rw [h0, Nat.cast_zero, ENat.WithBot.add_one_le_zero_iff, projectiveDimension_eq_bot_iff,
        ModuleCat.isZero_iff_subsingleton] at hih
      exact absurd hih (not_subsingleton M)
    · have hsplit : d - ms.length = (d - (ms.length + 1)) + 1 := by omega
      rw [hsplit, Nat.cast_add, ← Nat.cast_one (R := WithBot ℕ∞)] at hih
      exact ENat.WithBot.add_le_add_natCast_right_iff.mp hih

theorem AuslanderBuchsbaumProjDimUpper.proof : AuslanderBuchsbaumProjDimUpper.Statement := by
  intro R _ _ _ M _ _ _ _ n d ms hM hd hms hreg
  exact hasProjectiveDimensionLE_sub_length_of_isWeaklyRegular R d hd ms M n hM hms hreg

end GroundTheory.Heights₂.Heights
end
