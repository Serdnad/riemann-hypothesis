module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle025
import GroundTheory.ArithmeticGeometry.EtaleCompletion.Bundle001
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularUFD
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle046
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionAnalytic
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolomorphicFibreSumInt
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle047
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle071
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle050
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle076
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle060
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle088
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
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
public import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle001

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem adicCompletion_isLocalRing_of_isMaximal {A : Type*} [CommRing A] (m : Ideal A) [m.IsMaximal]
    (fg : m.FG) : IsLocalRing (AdicCompletion m A) := by
  have := AdicCompletion.isMaximal_map_of_le m m le_rfl fg
  have := AdicCompletion.isAdicComplete_self m fg
  exact isLocalRing_of_isAdicComplete_maximal (m.map (algebraMap A (AdicCompletion m A)))

theorem AffineCompletionNormal.proof (hF : FlatNormalFibres.Statement) (hR : FormalFibresRegular.Statement) :
    AffineCompletionNormal.Statement := by
  intro σ _ I m hI hIC hm
  have : I.IsPrime := hI
  have : m.IsMaximal := hm
  have hloc := adicCompletion_isLocalRing_of_isMaximal m (Ideal.fg_of_isNoetherianRing m)
  refine hF (MvPolynomial σ ℂ ⧸ I) (AdicCompletion m (MvPolynomial σ ℂ ⧸ I)) inferInstance inferInstance hloc
    inferInstance inferInstance hIC fun P _ => ?_
  have := hR ℂ (MvPolynomial σ ℂ ⧸ I) inferInstance m hm P
  exact ⟨inferInstance, GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isIntegrallyClosed _⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Metric Filter Topology Set

noncomputable section

namespace BranchInComponent

theorem differentiable_eval {n : ℕ} (g : MvPolynomial (Fin n) ℂ) :
    Differentiable ℂ (fun x : Fin n → ℂ => eval x g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp only [eval_C]; exact differentiable_const a
  | add p q hp hq => simp only [map_add (f := _)]; exact hp.add hq
  | mul_X p i hp => simp only [map_mul, eval_X]; exact hp.mul (differentiable_apply i)

theorem exists_open_prod_ne_zero {k : ℕ} {U : Set (Fin k → ℂ)} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hne : U.Nonempty) {ι : Type*} (s : Finset ι) (f : ι → (Fin k → ℂ) → ℂ)
    (hf : ∀ i ∈ s, AnalyticOnNhd ℂ (f i) U) (hnz : ∀ i ∈ s, ¬ EqOn (f i) 0 U) :
    ∃ V ⊆ U, IsOpen V ∧ V.Nonempty ∧ ∀ x ∈ V, ∏ i ∈ s, f i x ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨U, subset_rfl, hU, hne, fun x _ => by simp⟩
  | insert a s ha ih =>
    obtain ⟨V, hVU, hVo, ⟨z, hz⟩, hV⟩ :=
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) (fun i hi => hnz i (Finset.mem_insert_of_mem hi))
    have hfa := hf a (Finset.mem_insert_self a s)
    obtain ⟨w, hwV, hw⟩ : ∃ w ∈ V, f a w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      refine hnz a (Finset.mem_insert_self a s)
        (hfa.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc (hVU hz) ?_)
      filter_upwards [hVo.mem_nhds hz] with x hx using hcon x hx
    refine ⟨V ∩ f a ⁻¹' {0}ᶜ, inter_subset_left.trans hVU,
      (hfa.continuousOn.mono hVU).isOpen_inter_preimage hVo isOpen_compl_singleton, ⟨w, hwV, hw⟩, ?_⟩
    rintro x ⟨hxV, hx⟩
    rw [Finset.prod_insert ha]
    exact mul_ne_zero hx (hV x hxV)

theorem proof : BranchInComponent.Statement := by
  classical
  intro n I k q c
  by_contra hcon
  push Not at hcon
  set B : Set (Fin k → ℂ) := ball 0 c.radius with hB
  have hBo : IsOpen B := isOpen_ball
  have hBc : IsPreconnected B := (convex_ball (0 : Fin k → ℂ) c.radius).isPreconnected
  have hBne : B.Nonempty := ⟨0, mem_ball_self c.radius_pos⟩
  have hfin : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ I

  have hch : ∀ J : I.minimalPrimes, ∃ g ∈ (J : Ideal (MvPolynomial (Fin n) ℂ)),
      ¬ EqOn (fun τ => eval (c.toFun τ) g) 0 B := by
    intro J
    have hJ := hcon J J.2
    simp only [Set.MapsTo, not_forall, exists_prop] at hJ
    obtain ⟨τ, hτB, hτZ⟩ := hJ
    simp only [zeroSet, mem_ofPred_eq, not_forall] at hτZ
    obtain ⟨g, hg, hgτ⟩ := hτZ
    exact ⟨g, hg, fun h => hgτ (h hτB)⟩
  choose g hgJ hgnz using hch
  let _ : Fintype I.minimalPrimes := hfin.fintype
  have han : ∀ J : I.minimalPrimes, AnalyticOnNhd ℂ (fun τ => eval (c.toFun τ) (g J)) B := fun J =>
    IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionAnalytic.analyticOnNhd_of_differentiableOn hBo
      ((differentiable_eval (g J)).comp_differentiableOn c.differentiableOn)
  obtain ⟨V, hVB, -, ⟨x, hx⟩, hV⟩ := exists_open_prod_ne_zero hBo hBc hBne Finset.univ
    (fun J τ => eval (c.toFun τ) (g J)) (fun J _ => han J) (fun J _ => hgnz J)

  set G : MvPolynomial (Fin n) ℂ := ∏ J : I.minimalPrimes, g J with hG
  have hGrad : G ∈ I.radical := by
    rw [← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
    intro J hJ
    rw [hG, ← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ ⟨J, hJ⟩)]
    exact Ideal.mul_mem_right _ _ (hgJ ⟨J, hJ⟩)
  obtain ⟨N, hN⟩ := hGrad
  have h0 := c.mapsTo (hVB hx) _ hN
  rw [map_pow, hG, map_prod] at h0
  exact hV x hx (pow_eq_zero_iff'.1 h0).1

end BranchInComponent

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

namespace BranchChartInt

theorem analyticOnNhd_of_differentiableOn {k m : ℕ} {U : Set (Fin k → ℂ)} {f : (Fin k → ℂ) → Fin m → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := by
  refine analyticOnNhd_pi_iff.2 fun j => ?_
  have hj : DifferentiableOn ℂ (fun t => f t j) U := differentiableOn_pi.1 hf j
  refine IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hU hj.continuousOn fun w hw i => ?_
  have hw : DifferentiableAt ℂ (fun t => f t j) (Function.update w i (w i)) := by
    rw [Function.update_eq_self]
    exact (hj w hw).differentiableAt (hU.mem_nhds hw)
  exact hw.comp (w i) (hasFDerivAt_update w (w i)).differentiableAt

theorem differentiable_mulVec {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) :
    Differentiable ℂ (fun x : Fin n → ℂ => A *ᵥ x) :=
  (Matrix.mulVecLin A).toContinuousLinearMap.differentiable


open Classical in
theorem chartDens_indicator_image {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    {p : Fin n → ℂ} (γ : VarBranch J d p) (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (y : Fin d → ℂ) :
    chartDens J A (γ.image.indicator g) φ y =
      ∑ᶠ t ∈ {t | t ∈ Metric.ball (0 : Fin d → ℂ) γ.radius ∧ A *ᵥ γ.toFun t = y},
        (if h : ∃ s, IsSheetAt J A (γ.toFun t) s then
          g (γ.toFun t) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) (A *ᵥ γ.toFun t) else 0) := by
  set T : (Fin n → ℂ) → ℝ := fun x => if h : ∃ s, IsSheetAt J A x s then
      γ.image.indicator g x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) y else 0 with hT
  have h1 : chartDens J A (γ.image.indicator g) φ y = ∑ᶠ x ∈ fibre J A y, T x := rfl
  have h2 : ∑ᶠ x ∈ fibre J A y, T x =
      ∑ᶠ x ∈ γ.toFun '' {t | t ∈ Metric.ball (0 : Fin d → ℂ) γ.radius ∧ A *ᵥ γ.toFun t = y}, T x := by
    apply finsum_mem_inter_support_eq
    ext x
    simp only [Set.mem_inter_iff, Function.mem_support]
    constructor
    · rintro ⟨hx, hTx⟩
      have hxi : x ∈ γ.image := by
        by_contra hni
        apply hTx
        simp only [hT, Set.indicator_of_notMem hni, zero_mul, dite_eq_ite, ite_self]
      obtain ⟨t, ht, rfl⟩ := hxi
      exact ⟨⟨t, ⟨ht, hx.2⟩, rfl⟩, hTx⟩
    · rintro ⟨⟨t, ⟨ht, hty⟩, rfl⟩, hTx⟩
      exact ⟨⟨γ.mapsTo ht, hty⟩, hTx⟩
  have hinj : Set.InjOn γ.toFun {t | t ∈ Metric.ball (0 : Fin d → ℂ) γ.radius ∧ A *ᵥ γ.toFun t = y} :=
    γ.injOn.mono (by intro t ht; exact ht.1)
  rw [h1, h2, finsum_mem_image hinj]
  refine finsum_mem_congr rfl fun t ht => ?_
  have hti : γ.toFun t ∈ γ.image := ⟨t, ht.1, rfl⟩
  simp only [hT, Set.indicator_of_mem hti, ht.2]

theorem maDens_branch_eq {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {p : Fin n → ℂ} (γ : VarBranch J d p) {φ : Fin d → (Fin n → ℂ) → ℝ}
    (hφ : ∀ k, SmoothNear (zeroSet J) (φ k)) {t : Fin d → ℂ} (ht : t ∈ Metric.ball (0 : Fin d → ℂ) γ.radius)
    {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A (γ.toFun t) s) :
    ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ γ.toFun) t =
      ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (A *ᵥ γ.toFun t) *
        Complex.normSq (jacC (fun t => A *ᵥ γ.toFun t) t).det := by
  obtain ⟨U, hUo, hxU, hsd, hsx, -, V, hV, hVeq⟩ := hs
  set τ : (Fin d → ℂ) → Fin d → ℂ := fun t => A *ᵥ γ.toFun t with hτ
  have hτd : DifferentiableOn ℂ τ (Metric.ball 0 γ.radius) :=
    (differentiable_mulVec A).comp_differentiableOn γ.differentiableOn
  have hτa : AnalyticAt ℂ τ t := analyticOnNhd_of_differentiableOn Metric.isOpen_ball hτd t ht
  have hΔ : Metric.ball (0 : Fin d → ℂ) γ.radius ∈ 𝓝 t := Metric.isOpen_ball.mem_nhds ht
  have hγc : ContinuousAt γ.toFun t := γ.differentiableOn.continuousOn.continuousAt hΔ
  have hev : ∀ k, φ k ∘ γ.toFun =ᶠ[𝓝 t] (φ k ∘ s) ∘ τ := by
    intro k
    filter_upwards [hΔ, hγc.preimage_mem_nhds hV,
      hτa.continuousAt.preimage_mem_nhds (hUo.mem_nhds hxU)] with t' ht' hV' hU'
    simp only [Function.comp_apply]
    rw [← hVeq (γ.toFun t') ⟨γ.mapsTo ht', hV'⟩ hU']
  have hmd : ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ γ.toFun) t =
      ReciprocityTheory.AnForm.maDens (fun k => (φ k ∘ s) ∘ τ) t := by
    unfold ReciprocityTheory.AnForm.maDens
    congr 3
    funext k
    have h2 : fderiv ℝ (fderiv ℝ (φ k ∘ γ.toFun)) t = fderiv ℝ (fderiv ℝ ((φ k ∘ s) ∘ τ)) t :=
      ((hev k).fderiv (𝕜 := ℝ)).fderiv_eq
    unfold ReciprocityTheory.AnForm.hessC
    rw [h2]
  have hsa : AnalyticAt ℂ s (τ t) := analyticOnNhd_of_differentiableOn hUo hsd (τ t) hxU
  have hc : ∀ k, ContDiffAt ℝ 2 (φ k ∘ s) (τ t) := by
    intro k
    obtain ⟨O, hOo, hZO, hφO⟩ := hφ k
    have hmem : s (τ t) ∈ O := by
      rw [show s (τ t) = γ.toFun t from hsx]
      exact hZO (γ.mapsTo ht)
    exact ((hφO.contDiffAt (hOo.mem_nhds hmem)).of_le (WithTop.coe_le_coe.2 le_top)).comp (τ t)
      (hsa.contDiffAt.restrict_scalars ℝ)
  rw [hmd]
  exact maDens_comp (fun k => φ k ∘ s) τ t hτa hc

theorem integrableOn_branch {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ}
    (γ : VarBranch J d p) {g : (Fin n → ℂ) → ℝ} {φ : Fin d → (Fin n → ℂ) → ℝ} (hg : Continuous g)
    (hφ : ∀ k, SmoothNear (zeroSet J) (φ k))
    (hK : ∃ K : Set (Fin d → ℂ), IsCompact K ∧ K ⊆ Metric.ball 0 γ.radius ∧
      ∀ t ∈ Metric.ball 0 γ.radius, t ∉ K → g (γ.toFun t) = 0) :
    IntegrableOn (fun t => (g ∘ γ.toFun) t * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ γ.toFun) t)
      (Metric.ball 0 γ.radius) := by
  obtain ⟨K, hKc, hKΔ, hK0⟩ := hK
  have hγ : ContDiffOn ℝ 2 γ.toFun (Metric.ball 0 γ.radius) :=
    ((analyticOnNhd_of_differentiableOn Metric.isOpen_ball γ.differentiableOn).contDiffOn_of_completeSpace
      ).restrict_scalars ℝ
  have hc2 : ∀ k, ContDiffOn ℝ 2 (φ k ∘ γ.toFun) (Metric.ball 0 γ.radius) := by
    intro k
    obtain ⟨O, -, hZO, hφO⟩ := hφ k
    exact (hφO.of_le (WithTop.coe_le_coe.2 le_top)).comp hγ fun t ht => hZO (γ.mapsTo ht)
  have hcont : ContinuousOn (fun t => (g ∘ γ.toFun) t * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ γ.toFun) t)
      (Metric.ball 0 γ.radius) :=
    (hg.comp_continuousOn γ.differentiableOn.continuousOn).mul
      (ReciprocityTheory.AnForm.M.maDens_continuousOn _ _ Metric.isOpen_ball hc2)
  refine ((hcont.mono hKΔ).integrableOn_compact hKc).of_forall_sdiff_eq_zero measurableSet_ball ?_
  rintro t ⟨htΔ, htK⟩
  simp [hK0 t htΔ htK]

end BranchChartInt


open BranchChartInt in
theorem BranchChartInt.proof (hA : HolomorphicFibreSumInt.Statement) (hS : BranchSheetAE.Statement)
    (hF : ComplexSets.FibreBound.Statement) : BranchChartInt.Statement := by
  classical
  intro n d J A p γ g φ hJ hdim hfin hg hφ hK
  set Δ := Metric.ball (0 : Fin d → ℂ) γ.radius with hΔ
  set τ : (Fin d → ℂ) → Fin d → ℂ := fun t => A *ᵥ γ.toFun t with hτ
  set H : (Fin d → ℂ) → ℝ := fun t => if h : ∃ s, IsSheetAt J A (γ.toFun t) s then
      g (γ.toFun t) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) (A *ᵥ γ.toFun t) else 0 with hH
  have hτd : DifferentiableOn ℂ τ Δ := (differentiable_mulVec A).comp_differentiableOn γ.differentiableOn
  have hFin : ∀ y, {t | t ∈ Δ ∧ τ t = y}.Finite := by
    intro y
    refine Set.Finite.of_finite_image ((hF n d J A hJ hdim hfin y).2.1.subset ?_)
      (γ.injOn.mono fun t ht => ht.1)
    rintro x ⟨t, ⟨ht, hty⟩, rfl⟩
    exact ⟨γ.mapsTo ht, hty⟩
  have hae : ∀ᵐ t ∂(volume.restrict Δ), (g ∘ γ.toFun) t * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ γ.toFun) t =
      Complex.normSq (jacC τ t).det * H t := by
    filter_upwards [hS n d J A p γ hJ hdim hfin, ae_restrict_mem measurableSet_ball] with t hts htΔ
    simp only [hH, dif_pos hts, Function.comp_apply]
    rw [maDens_branch_eq γ hφ htΔ hts.choose_spec]
    ring
  have hint : IntegrableOn (fun t => Complex.normSq (jacC τ t).det * H t) Δ :=
    (integrableOn_branch γ hg hφ hK).congr hae
  obtain ⟨hIi, hIeq⟩ := hA d Δ τ H Metric.isOpen_ball hτd hFin hint
  have hcd : chartDens J A (γ.image.indicator g) φ = fun y => ∑ᶠ t ∈ {t | t ∈ Δ ∧ τ t = y}, H t :=
    funext fun y => chartDens_indicator_image J A γ g φ y
  refine ⟨hcd ▸ hIi, ?_⟩
  unfold chartInt ReciprocityTheory.AnForm.maInt
  rw [hcd, hIeq]
  exact (integral_congr_ae hae).symm

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace BranchSheetAE

variable {d : ℕ}

theorem volume_preimage_null {G : Set (Fin d → ℂ)} {F : (Fin d → ℂ) → Fin d → ℂ} (hG : IsOpen G)
    (hF : DifferentiableOn ℂ F G) (hdet : ∀ w ∈ G, (ReciprocityTheory.AnForm.A.jacC F w).det ≠ 0)
    {N : Set (Fin d → ℂ)} (hN : volume N = 0) :
    volume {t | t ∈ G ∧ F t ∈ N} = 0 := by
  have hFa := SheetOnlyNull.analyticOnNhd_of_differentiableOn hG hF
  have hequiv : ∀ w ∈ G, ∃ e : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ),
      HasStrictFDerivAt F (e : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) w := by
    intro w hw
    have hinj : Function.Injective (fderiv ℂ F w) :=
      (SheetOnlyNull.injective_iff_det_ne_zero _).2 (by rw [← ReciprocityTheory.AnForm.A.det_jacC]; exact hdet w hw)
    refine ⟨(LinearEquiv.ofInjectiveEndo _ hinj).toContinuousLinearEquiv, ?_⟩
    exact (hFa w hw).hasStrictFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
  apply measure_null_of_locally_null
  rintro x ⟨hxG, -⟩
  obtain ⟨e, he⟩ := hequiv x hxG
  set φ := he.toOpenPartialHomeomorph F with hφdef
  have hφ : ∀ w, φ w = F w := fun w => by rw [hφdef, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
  have hsymd : DifferentiableOn ℝ φ.symm (φ.target ∩ φ.symm ⁻¹' G) := by
    rintro z ⟨hzT, hzG⟩
    obtain ⟨e', he'⟩ := hequiv _ hzG
    have hd : HasFDerivAt φ.symm _ z :=
      φ.hasFDerivAt_symm hzT (f' := e') (by
        have : (φ : (Fin d → ℂ) → Fin d → ℂ) = F := funext hφ
        rw [this]; exact he'.hasFDerivAt)
    exact (hd.differentiableAt.restrictScalars ℝ).differentiableWithinAt
  refine ⟨{t | t ∈ G ∧ F t ∈ N} ∩ φ.source,
    inter_mem_nhdsWithin _ (φ.open_source.mem_nhds he.mem_toOpenPartialHomeomorph_source), ?_⟩
  refine measure_mono_null ?_ (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (μ := volume) (hsymd.mono Set.inter_subset_left) (measure_mono_null Set.inter_subset_right hN))
  rintro t ⟨⟨htG, htN⟩, hts⟩
  refine ⟨φ t, ⟨⟨φ.map_source hts, ?_⟩, ?_⟩, φ.left_inv hts⟩
  · show φ.symm (φ t) ∈ G
    rw [φ.left_inv hts]; exact htG
  · rw [hφ]; exact htN

end BranchSheetAE

theorem BranchSheetAE.proof (h₁ : IndefiniteRowSideFullHecke.ComplexSets.RankDeficientFibreInfinite.Statement)
    (h₂ : ComplexSets.FibreBound.Statement) (h₃ : DiscriminantSheetCover.Statement) :
    BranchSheetAE.Statement := by
  intro n d J A p γ hJ hdim hA
  set Δ := Metric.ball (0 : Fin d → ℂ) γ.radius with hΔ
  set τ : (Fin d → ℂ) → Fin d → ℂ := fun t => A *ᵥ γ.toFun t with hτdef
  have hΔo : IsOpen Δ := Metric.isOpen_ball
  have hτd : DifferentiableOn ℂ τ Δ := SheetOnlyNull.differentiableOn_mulVec A γ.differentiableOn
  have hdeta := SheetOnlyNull.analyticOnNhd_det_jacC hΔo hτd
  have hne : ∃ z ∈ Δ, (ReciprocityTheory.AnForm.A.jacC τ z).det ≠ 0 := by
    by_contra hall
    push Not at hall
    obtain ⟨y, hy⟩ := h₁ d d Δ τ hΔo ⟨0, Metric.mem_ball_self γ.radius_pos⟩ hτd fun v hv hinj =>
      (SheetOnlyNull.injective_iff_det_ne_zero _).1 hinj
        (by rw [← ReciprocityTheory.AnForm.A.det_jacC]; exact hall v hv)
    have hinf : (γ.toFun '' {t | t ∈ Δ ∧ τ t = y}).Infinite :=
      (Set.infinite_image_iff (γ.injOn.mono fun t (ht : t ∈ {t | t ∈ Δ ∧ τ t = y}) => ht.1)).2 hy
    refine hinf ((h₂ n d J A hJ hdim hA y).2.1.subset ?_)
    rintro _ ⟨t, ⟨htΔ, hty⟩, rfl⟩
    exact ⟨γ.mapsTo htΔ, hty⟩
  have hZ := ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd hΔo (convex_ball _ _).isPreconnected
    hdeta hne
  obtain ⟨P, U, D, N, s, -, hUD, -, -, hnull, hfib⟩ := h₃ n d J A hJ hdim hA
  set G := Δ ∩ (fun t => (ReciprocityTheory.AnForm.A.jacC τ t).det) ⁻¹' {0}ᶜ with hGdef
  have hG : IsOpen G := hdeta.continuousOn.isOpen_inter_preimage hΔo isOpen_compl_singleton
  have hS := BranchSheetAE.volume_preimage_null hG (hτd.mono Set.inter_subset_left)
    (fun w hw => hw.2) hnull
  rw [ae_restrict_iff' hΔo.measurableSet, ae_iff]
  refine measure_mono_null ?_ (measure_union_null hZ hS)
  intro t ht
  simp only [Set.mem_ofPred_eq, Classical.not_imp] at ht
  obtain ⟨htΔ, hno⟩ := ht
  by_cases hdt : (ReciprocityTheory.AnForm.A.jacC τ t).det = 0
  · exact Or.inl ⟨htΔ, hdt⟩
  refine Or.inr ⟨⟨htΔ, hdt⟩, fun hD => hno ?_⟩
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hD
  obtain ⟨hfibk, -, hsh⟩ := hfib k (τ t) ((hUD k).2.2.1 hk)
  have hmem : γ.toFun t ∈ fibre J A (τ t) := ⟨γ.mapsTo htΔ, rfl⟩
  rw [hfibk] at hmem
  obtain ⟨j, hj⟩ := hmem
  exact ⟨s k j, hj ▸ hsh j⟩

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def GermProjectionFunctionForm.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (p : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    (∀ i, AnalyticAt ℂ (p i) w) → IsFiniteGermProjection w (holGermIdeal w p) A →
      (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → IsGermCombination w p (fun z => h (A z)) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) ∧
      (∀ i : σ, ∃ (n : ℕ) (b : Fin n → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (b j) (A w)) ∧
        IsGermCombination w p (fun z => z i ^ n + ∑ j, b j (A z) * z i ^ (j : ℕ))) ∧
      (∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g w →
        ∃ (s : Finset (σ → ℕ)) (a : (σ → ℕ) → (Fin d → ℂ) → ℂ), (∀ m ∈ s, AnalyticAt ℂ (a m) (A w)) ∧
          IsGermCombination w p (fun z => g z - ∑ m ∈ s, a m (A z) * ∏ i, z i ^ m i))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
