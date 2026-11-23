module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle042
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.WeierstrassPolynomialRing
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle040
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle038
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle047
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle036
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle089
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle048
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle069
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle074
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle071
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Pi
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsSt
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Polynomial

noncomputable section

theorem coe_mkGerm {τ : Type} [Fintype τ] (f : (τ → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0) :
    ((mkGerm f hf : holGerms (0 : τ → ℂ)) : Germ (𝓝 (0 : τ → ℂ)) ℂ) = ↑f := rfl

theorem isUnit_mkGerm {τ : Type} [Fintype τ] (e : (τ → ℂ) → ℂ) (he : AnalyticAt ℂ e 0) (he0 : e 0 ≠ 0) :
    IsUnit (mkGerm e he) := by
  refine IsUnit.of_mul_eq_one (mkGerm (fun x => (e x)⁻¹) (he.inv he0)) (Subtype.ext ?_)
  show ((fun x => e x * (e x)⁻¹ : (τ → ℂ) → ℂ) : Germ (𝓝 (0 : τ → ℂ)) ℂ) =
    ((fun _ => (1 : ℂ) : (τ → ℂ) → ℂ) : Germ (𝓝 (0 : τ → ℂ)) ℂ)
  exact Germ.coe_eq.2 (by
    filter_upwards [he.continuousAt.eventually_ne he0] with x hx
    exact mul_inv_cancel₀ hx)

theorem uniqueFactorizationMonoid_holGerms_option (hN : AnalyticGermsNoetherian.Statement)
    (hG : GeneralLinearCoordinates.Statement) (hP : WeierstrassPreparation.Statement)
    (hD : WeierstrassDivision.Statement) (σ : Type) [Fintype σ]
    (hR : UniqueFactorizationMonoid (holGerms (0 : σ → ℂ))) :
    UniqueFactorizationMonoid (holGerms (0 : Option σ → ℂ)) := by
  have := hN (Option σ) 0
  have := hR
  refine { irreducible_iff_prime := fun {φ} => ⟨fun hφ => ?_, Prime.irreducible⟩ }
  obtain ⟨f, hf, hfφ⟩ := φ.2
  have hnz : ¬ ∀ᶠ x in 𝓝 (0 : Option σ → ℂ), f x = 0 := fun h =>
    hφ.ne_zero (Subtype.ext (by rw [← hfφ]; exact Germ.coe_eq.2 h))
  obtain ⟨A, d, hAd⟩ := hG σ f hf hnz
  have hfA : AnalyticAt ℂ (f ∘ A) 0 := hf.comp_of_eq (A.analyticAt 0) (map_zero A)

  have hT : germAffineEquiv A (0 : Option σ → ℂ) φ = mkGerm (f ∘ A) hfA := by
    apply Subtype.ext
    show ((germPull (fun z : Option σ → ℂ => A z + 0) ((A.analyticAt 0).add analyticAt_const) (by simp) φ : holGerms (0 : Option σ → ℂ)) :
      Germ (𝓝 (0 : Option σ → ℂ)) ℂ) = ↑(f ∘ A)
    rw [germPull_coe _ _ _ φ f hfφ]
    simp only [add_zero]
  refine (MulEquiv.prime_iff (germAffineEquiv A (0 : Option σ → ℂ))).1 ?_
  rw [hT]
  have hirrA : Irreducible (mkGerm (f ∘ A) hfA) := by
    rw [← hT]; exact (MulEquiv.irreducible_iff (germAffineEquiv A (0 : Option σ → ℂ))).2 hφ

  obtain ⟨e, c, he, he0, hc, hc0, hfe⟩ := hP σ d (f ∘ A) hfA hAd
  have hE := isUnit_mkGerm e he he0
  have hF : mkGerm (f ∘ A) hfA = polyToGerm σ (weierstrassPoly c hc) * mkGerm e he := by
    apply Subtype.ext
    rw [Subring.coe_mul, polyToGerm_weierstrassPoly, coe_mkGerm, coe_mkGerm, ← Germ.coe_mul]
    exact Germ.coe_eq.2 (by
      filter_upwards [hfe] with x hx
      rw [hx, Pi.mul_apply, mul_comm])
  have hassoc : Associated (polyToGerm σ (weierstrassPoly c hc)) (mkGerm (f ∘ A) hfA) :=
    ⟨hE.unit, by rw [hF, IsUnit.unit_spec]⟩
  have hirrW : Irreducible (polyToGerm σ (weierstrassPoly c hc)) := hassoc.irreducible_iff.2 hirrA
  refine hassoc.prime_iff.1 ?_

  have hprimeω : Prime (weierstrassPoly c hc) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.1 (weierstrassPoly_irreducible c hc hc0 hirrW)
  refine prime_map_of_prime (polyToGerm σ) hprimeω hirrW.ne_zero ?_
    (weierstrassPoly_dvd_of_polyToGerm_dvd c hc hc0)
  intro g
  obtain ⟨g₀, hg₀, hg₀g⟩ := g.2
  obtain ⟨q, a, hq, ha, hdiv⟩ := hD σ d (f ∘ A) g₀ hfA hg₀ hAd
  refine ⟨mkGerm (q * e) (hq.mul he), finPoly fun j => mkGerm (a j) (ha j), Subtype.ext ?_⟩
  rw [Subring.coe_add, Subring.coe_mul, polyToGerm_weierstrassPoly, polyToGerm_finPoly, coe_mkGerm, ← hg₀g,
    ← Germ.coe_mul, ← Germ.coe_add]
  exact Germ.coe_eq.2 (by
    filter_upwards [hdiv, hfe] with x hx hx'
    simp only [Pi.add_apply, Pi.mul_apply]
    rw [hx, hx']
    ring)

theorem HolGermsUFD.proof (hP : WeierstrassPreparation.Statement) (hD : WeierstrassDivision.Statement) :
    HolGermsUFD.Statement := by
  have hG := GeneralLinearCoordinates.proof
  have hN := AnalyticGermsNoetherian.proof hD hG
  have hfin : ∀ n : ℕ, UniqueFactorizationMonoid (holGerms (0 : Fin n → ℂ)) := by
    intro n
    induction n with
    | zero =>
      let _ := isField_holGerms_fin_zero.toField
      infer_instance
    | succ n ih =>
      exact (germAffineEquiv (LinearEquiv.funCongrLeft ℂ ℂ (finSuccEquiv n)).toContinuousLinearEquiv
        (0 : Fin (n + 1) → ℂ)).symm.toMulEquiv.uniqueFactorizationMonoid
        (uniqueFactorizationMonoid_holGerms_option hN hG hP hD (Fin n) ih)
  intro σ _ w
  exact (germAffineEquiv (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin σ)).toContinuousLinearEquiv
    w).symm.toMulEquiv.uniqueFactorizationMonoid (hfin _)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ENNReal

noncomputable section

namespace ChartMassCompact

variable {n d : ℕ}

theorem mdisc_coord_zero {D : ℕ} (M : Fin D → Matrix (Fin D) (Fin D) ℂ) (i : Fin D)
    (hi : M i = 0) : ReciprocityTheory.AnForm.mdisc M = 0 := by
  rw [ReciprocityTheory.AnForm.A.mdisc_eq_sum_polCoef]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun r _ => ?_)
  by_cases hr : Function.Surjective r
  · obtain ⟨j, hj⟩ := hr i
    refine mul_eq_zero_of_right _ (Matrix.det_eq_zero_of_row_eq_zero j fun k => ?_)
    simp [hj, hi]
  · rw [ReciprocityTheory.AnForm.A.polCoef_eq_zero r hr, zero_mul]

theorem hessC_eq_zero_of_eventuallyEq {D : ℕ} {φ : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : φ =ᶠ[𝓝 z] 0) : ReciprocityTheory.AnForm.hessC φ z = 0 := by
  have h1 : fderiv ℝ φ =ᶠ[𝓝 z] fderiv ℝ (0 : (Fin D → ℂ) → ℝ) := h.fderiv
  have h2 : fderiv ℝ (fderiv ℝ φ) z = 0 := by
    rw [h1.fderiv_eq]
    simp
  ext i j
  simp [ReciprocityTheory.AnForm.hessC, h2]

theorem maDens_eq_zero {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s)
    (ψ : Fin d → (Fin n → ℂ) → ℝ) (i : Fin d) (hx : x ∉ tsupport (ψ i)) :
    ReciprocityTheory.AnForm.maDens (fun k => ψ k ∘ s) (A *ᵥ x) = 0 := by
  obtain ⟨U, hU, hxU, hsd, hsx, -⟩ := hs
  have hcont : ContinuousAt s (A *ᵥ x) := (hsd.differentiableAt (hU.mem_nhds hxU)).continuousAt
  have hev : (ψ i ∘ s) =ᶠ[𝓝 (A *ᵥ x)] 0 := by
    have hnhds : (tsupport (ψ i))ᶜ ∈ 𝓝 (s (A *ᵥ x)) := by
      rw [hsx]
      exact (isClosed_tsupport _).isOpen_compl.mem_nhds hx
    filter_upwards [hcont.preimage_mem_nhds hnhds] with y hy
    show ψ i (s y) = 0
    exact image_eq_zero_of_notMem_tsupport hy
  unfold ReciprocityTheory.AnForm.maDens
  rw [mdisc_coord_zero _ i (hessC_eq_zero_of_eventuallyEq hev)]
  simp

theorem integrable_ball (hC : ChartMassCompare.Statement) (hMF : MassFinite.Statement)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (ψ : Fin d → (Fin n → ℂ) → ℝ)
    (hJ : J.IsPrime) (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d)
    (hA : IsFiniteProjection J A) (hψ : ∀ k, SmoothNear (zeroSet J) (ψ k)) (R : ℝ) :
    Integrable (chartAbsDens J A ((Metric.closedBall (0 : Fin n → ℂ) R).indicator fun _ => (1 : ℝ)) ψ) := by
  obtain ⟨K, hK, hle⟩ := hC n d J A ψ R hJ hd hA hψ
  have hmeas := (SheetSumMeasurable.proof n d J A
    ((Metric.closedBall (0 : Fin n → ℂ) R).indicator fun _ => (1 : ℝ)) ψ hJ hd hA
    (measurable_const.indicator Metric.isClosed_closedBall.measurableSet) hψ).2
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hbd : Bornology.IsBounded
      (WithLp.ofLp ⁻¹' Metric.closedBall (0 : Fin n → ℂ) R : Set (EuclideanSpace ℂ (Fin n))) :=
    (PiLp.antilipschitzWith_ofLp 2 fun _ : Fin n => ℂ).isBounded_preimage Metric.isBounded_closedBall
  obtain ⟨R', hR'⟩ := (Metric.isBounded_iff_subset_ball 0).1 hbd
  have h1 := hle (fun _ => 1) measurable_const
  simp only [enorm_one, setLIntegral_one] at h1
  refine h1.trans_lt (ENNReal.mul_lt_top hK ?_)
  exact (measure_mono (Set.inter_subset_inter_right _ hR')).trans_lt (hMF n d J hJ hd R')

theorem chartAbsDens_le (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (ψ : Fin d → (Fin n → ℂ) → ℝ) {K B : Set (Fin n → ℂ)} {M : ℝ}
    (hKB : K ⊆ B) (hM : ∀ x ∈ zeroSet J ∩ K, |f x| ≤ M) (hM0 : 0 ≤ M)
    (hvan : ∀ x s, IsSheetAt J A x s → x ∉ K →
      f x * ReciprocityTheory.AnForm.maDens (fun k => ψ k ∘ s) (A *ᵥ x) = 0)
    (y : Fin d → ℂ) (hfin : (fibre J A y).Finite) :
    chartAbsDens J A f ψ y ≤ M * chartAbsDens J A (B.indicator fun _ => 1) ψ y := by
  classical
  unfold chartAbsDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  obtain ⟨hxZ, rfl⟩ := hx
  split_ifs with h
  · dsimp only
    by_cases hxK : x ∈ K
    · rw [Set.indicator_of_mem (hKB hxK), one_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right (hM x ⟨hxZ, hxK⟩) (abs_nonneg _)
    · rw [hvan x _ h.choose_spec hxK, abs_zero]
      positivity
  · simp

end ChartMassCompact


open ChartMassCompact in
theorem ChartMassCompact.proof (hC : ChartMassCompare.Statement) (hMF : MassFinite.Statement) :
    ChartMassCompact.Statement := by
  classical
  intro n d J A f ψ hJ hd hA hf hψ hsupp
  obtain ⟨K, hKc, hvan⟩ : ∃ K : Set (Fin n → ℂ), IsCompact K ∧ ∀ x s, IsSheetAt J A x s → x ∉ K →
      f x * ReciprocityTheory.AnForm.maDens (fun k => ψ k ∘ s) (A *ᵥ x) = 0 := by
    rcases hsupp with hc | ⟨i, hc⟩
    · exact ⟨tsupport f, hc, fun x s _ hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]⟩
    · exact ⟨tsupport (ψ i), hc, fun x s hs hx => by rw [maDens_eq_zero hs ψ i hx, mul_zero]⟩
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hKc.isBounded
  obtain ⟨M, hM⟩ := (hKc.inter_left (SheetSumMeasurable.isClosed_zeroSet J)).exists_bound_of_continuousOn
    (hf.mono Set.inter_subset_left)
  have heq : chartAbsDens J A f ψ = chartAbsDens J A ((zeroSet J).piecewise f 0) ψ := by
    funext y
    unfold chartAbsDens sheetSum
    refine finsum_congr fun x => finsum_congr fun hx => ?_
    simp only [Set.piecewise_eq_of_mem _ _ _ hx.1]
  have hgm : Measurable ((zeroSet J).piecewise f 0) :=
    hf.measurable_piecewise continuousOn_const (SheetSumMeasurable.isClosed_zeroSet J).measurableSet
  have hmeas : AEStronglyMeasurable (chartAbsDens J A f ψ) volume := by
    rw [heq]
    exact (SheetSumMeasurable.proof n d J A _ ψ hJ hd hA hgm hψ).2.aestronglyMeasurable
  refine ((integrable_ball hC hMF J A ψ hJ hd hA hψ R).const_mul (max M 0)).mono' hmeas
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (chartAbsDens_nonneg _ _ _ _ _)]
  exact chartAbsDens_le J A f ψ hR (fun x hx => (Real.norm_eq_abs (f x) ▸ hM x hx).trans (le_max_left _ _))
    (le_max_right _ _) hvan y (FibreBound.proof n d J A hJ hd hA y).2.1

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ComplexSets

noncomputable section

namespace DivisorOneComponent

theorem mem_zeroSet_iff {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    q ∈ zeroSet K ↔ K ≤ RingHom.ker (eval q) :=
  ⟨fun h f hf => RingHom.mem_ker.2 (h f hf), fun h _ hf => RingHom.mem_ker.1 (h hf)⟩

theorem isClosed_zeroSet {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroSet K) := by
  have : zeroSet K = ⋂ f ∈ K, {x : Fin n → ℂ | eval x f = 0} := by ext x; simp [zeroSet]
  rw [this]
  exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval f) continuous_const

theorem exists_bound (d : ℕ) : ∃ N : WithBot ℕ∞, N < (d : WithBot ℕ∞) ∧
    ∀ x : WithBot ℕ∞, x + 1 ≤ (d : WithBot ℕ∞) → x ≤ N := by
  rcases d with _ | k
  · refine ⟨⊥, WithBot.bot_lt_coe _, fun x hx => ?_⟩
    cases x using WithBot.recBotCoe with
    | bot => exact le_rfl
    | coe y =>
      have : y + 1 ≤ 0 := by exact_mod_cast hx
      simp at this
  · refine ⟨(k : WithBot ℕ∞), by exact_mod_cast Nat.lt_succ_self k, fun x hx => ?_⟩
    cases x using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe y =>
      have h1 : y + 1 ≤ ((k + 1 : ℕ) : ℕ∞) := by exact_mod_cast hx
      have h2 : y ≤ (k : ℕ∞) := by
        cases y using ENat.recTopCoe with
        | top => simp at h1
        | coe y =>
          have h3 : y + 1 ≤ k + 1 := by exact_mod_cast h1
          exact_mod_cast (by omega : y ≤ k)
      exact_mod_cast h2

theorem dim_sup_add_one_le {n d : ℕ} {J W W' : Ideal (MvPolynomial (Fin n) ℂ)} [J.IsPrime] {u : Fin n → ℂ}
    (hu : linForm u ∉ J) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((d + 1 : ℕ) : WithBot ℕ∞))
    (hW : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes)
    (hW' : W' ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes) (hne : W ≠ W') :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (W ⊔ W')) + 1 ≤ (d : WithBot ℕ∞) := by
  have _ : W.IsPrime := hW.1.1
  obtain ⟨x, hxW', hxW⟩ : ∃ x ∈ W', x ∉ W := by
    by_contra! h
    exact hne (le_antisymm (hW.2 hW'.1 h) h)
  have hle : W ⊔ Ideal.span {x} ≤ W ⊔ W' := sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).2 hxW') _
  have hx : x ∈ W ⊔ Ideal.span {x} := Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)
  have hr : Ideal.Quotient.mk W x ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ W) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have hsurj : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (W ⊔ W')) ≤
      ringKrullDim ((MvPolynomial (Fin n) ℂ ⧸ W) ⧸ Ideal.span {Ideal.Quotient.mk W x}) := by
    refine ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ (Ideal.Quotient.factor
      (le_sup_left.trans hle)) ?_) (Ideal.Quotient.lift_surjective_of_surjective _ _
        (Ideal.Quotient.factor_surjective _))
    intro y hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
    have h0 : Ideal.Quotient.mk (W ⊔ W') (c' * x) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_left _ _ (hle hx))
    simpa [Ideal.Quotient.factor_mk, map_mul] using h0
  calc ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (W ⊔ W')) + 1
      ≤ ringKrullDim ((MvPolynomial (Fin n) ℂ ⧸ W) ⧸ Ideal.span {Ideal.Quotient.mk W x}) + 1 := by gcongr
    _ ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr
    _ = (d : WithBot ℕ∞) := ringKrullDim_component hu hW hdim

end DivisorOneComponent


open DivisorOneComponent in
theorem DivisorOneComponent.proof : DivisorOneComponent.Statement := by
  classical
  intro n d J u hJ hdim hu
  have hKq : ∀ x ∈ zeroSet J, linEval u x = 0 → J ⊔ Ideal.span {linForm u} ≤ RingHom.ker (eval x) := by
    intro x hxJ hxu
    refine sup_le ((mem_zeroSet_iff J x).1 hxJ) ((Ideal.span_singleton_le_iff_mem _).2 ?_)
    simpa [linForm, linEval] using hxu
  generalize hK : J ⊔ Ideal.span {linForm u} = K at hKq ⊢
  have hM : K.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ K
  obtain ⟨S, hS⟩ : ∃ S : Finset (Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ)),
      ∀ p, p ∈ S ↔ p.1 ∈ K.minimalPrimes ∧ p.2 ∈ K.minimalPrimes ∧ p.1 ≠ p.2 :=
    ⟨(hM.prod hM).toFinset.filter fun p => p.1 ≠ p.2, fun p => by rw [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_prod, and_assoc]⟩
  obtain ⟨I, hI⟩ : ∃ I, I = S.inf fun p => p.1 ⊔ p.2 := ⟨_, rfl⟩
  have hmemS : ∀ p ∈ S, p.1 ∈ K.minimalPrimes ∧ p.2 ∈ K.minimalPrimes ∧ p.1 ≠ p.2 := fun p hp => (hS p).1 hp
  have hpair : ∀ W W', W ∈ K.minimalPrimes → W' ∈ K.minimalPrimes → W ≠ W' → I ≤ W ⊔ W' :=
    fun W W' hW hW' hne => by
      have h := Finset.inf_le (f := fun p : Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ) => p.1 ⊔ p.2) ((hS (W, W')).2 ⟨hW, hW', hne⟩)
      rw [hI]; exact h
  have hKI : K ≤ I := by
    have h := Finset.le_inf (f := fun p : Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ) => p.1 ⊔ p.2) (a := K) (s := S) fun p hp => (hmemS p hp).1.1.2.trans le_sup_left
    rw [hI]; exact h
  obtain ⟨N, hN, hxN⟩ := exists_bound d
  refine ⟨I, hKI, ?_, ?_⟩
  · refine lt_of_le_of_lt (ComplexSets.quotient_dim_le_of_minimalPrimes I fun Z hZ => ?_) hN
    have hZI : S.inf (fun p : Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ) => p.1 ⊔ p.2) ≤ Z := by rw [← hI]; exact hZ.1.2
    obtain ⟨p, hp, hpZ⟩ := (Ideal.IsPrime.inf_le' (f := fun p : Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ) => p.1 ⊔ p.2) hZ.1.1).1 hZI
    obtain ⟨h1, h2, h12⟩ := hmemS p hp
    exact (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hpZ)).trans
      (hxN _ (dim_sup_add_one_le hu hdim (by rw [hK]; exact h1) (by rw [hK]; exact h2) h12))
  · intro q hqJ hqu hqI
    obtain ⟨W, hW, hWq⟩ := Ideal.exists_minimalPrimes_le (hKq q hqJ hqu)
    have huniq : ∀ W' ∈ K.minimalPrimes, q ∈ zeroSet W' → W' = W := by
      intro W' hW' hq'
      by_contra hne
      exact hqI ((mem_zeroSet_iff I q).2 ((hpair W W' hW hW' (Ne.symm hne)).trans
        (sup_le hWq ((mem_zeroSet_iff W' q).1 hq'))))
    refine ⟨W, hW, (mem_zeroSet_iff W q).2 hWq, huniq, ⋂ W' ∈ K.minimalPrimes \ {W}, (zeroSet W')ᶜ, ?_, ?_⟩
    · refine (biInter_mem (hM.subset Set.sdiff_subset)).2 fun W' hW' => (isClosed_zeroSet W').isOpen_compl.mem_nhds ?_
      exact fun hq' => hW'.2 (huniq W' hW'.1 hq')
    · rintro x ⟨hxJ, hxU⟩ hxu
      obtain ⟨W'', hW'', hW''x⟩ := Ideal.exists_minimalPrimes_le (hKq x hxJ hxu)
      by_cases h : W'' = W
      · subst h; exact (mem_zeroSet_iff W'' x).2 hW''x
      · exact absurd ((mem_zeroSet_iff W'' x).2 hW''x) (Set.mem_iInter₂.1 hxU W'' ⟨hW'', h⟩)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology ComplexSets
open scoped ContDiff

noncomputable section

theorem ParamDensIntegrable.analyticOnNhd_of_differentiableOn {k m : ℕ} {U : Set (Fin k → ℂ)}
    {f : (Fin k → ℂ) → Fin m → ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := by
  refine analyticOnNhd_pi_iff.2 fun j => ?_
  have hj : DifferentiableOn ℂ (fun t => f t j) U := differentiableOn_pi.1 hf j
  refine IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hU hj.continuousOn fun w hw i => ?_
  have hw : DifferentiableAt ℂ (fun t => f t j) (Function.update w i (w i)) := by
    rw [Function.update_eq_self]
    exact (hj w hw).differentiableAt (hU.mem_nhds hw)
  exact hw.comp (w i) (hasFDerivAt_update w (w i)).differentiableAt

theorem ParamDensIntegrable.proof : ParamDensIntegrable.Statement := by
  intro n d W σ r r' N hσ hrr' hN f φ hf hfN hφ
  set B := Metric.ball (0 : Fin d → ℂ) r with hB
  choose U hUo hZU hφU using hφ
  set V : Set (Fin d → ℂ) := B ∩ σ ⁻¹' (⋂ k, U k) with hV
  have hσc : ContinuousOn σ B := hσ.continuousOn
  have hVo : IsOpen V := hσc.isOpen_inter_preimage Metric.isOpen_ball (isOpen_iInter_of_finite hUo)
  have hσ2 : ContDiffOn ℝ 2 σ B :=
    ((ParamDensIntegrable.analyticOnNhd_of_differentiableOn Metric.isOpen_ball hσ).contDiffOn_of_completeSpace).restrict_scalars ℝ
  have hc2 : ∀ k, ContDiffOn ℝ 2 (φ k ∘ σ) V := by
    intro k
    exact ((hφU k).of_le (WithTop.coe_le_coe.2 le_top)).comp (hσ2.mono Set.inter_subset_left)
      fun w hw => Set.mem_iInter.1 hw.2 k
  have hmaV : ContinuousOn (ReciprocityTheory.AnForm.maDens fun k => φ k ∘ σ) V :=
    ReciprocityTheory.AnForm.M.maDens_continuousOn _ _ hVo hc2
  have hcont : ContinuousOn (fun w => f (σ w) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ σ) w) B := by
    refine continuousOn_of_forall_continuousAt fun w hw => ?_
    by_cases hs : σ w ∈ tsupport f
    · have hwV : w ∈ V := ⟨hw, Set.mem_iInter.2 fun k => hZU k (hN w hw (hfN hs)).1⟩
      exact ((hf.continuousAt).comp (hσc.continuousAt (Metric.isOpen_ball.mem_nhds hw))).mul
        (hmaV.continuousAt (hVo.mem_nhds hwV))
    · have hO : IsOpen (B ∩ σ ⁻¹' (tsupport f)ᶜ) :=
        hσc.isOpen_inter_preimage Metric.isOpen_ball (isClosed_tsupport f).isOpen_compl
      refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [hO.mem_nhds ⟨hw, hs⟩] with w' hw'
      simp [image_eq_zero_of_notMem_tsupport hw'.2]
  have hK : IsCompact (Metric.closedBall (0 : Fin d → ℂ) r') := isCompact_closedBall 0 r'
  have hKB : Metric.closedBall (0 : Fin d → ℂ) r' ⊆ B := Metric.closedBall_subset_ball hrr'
  refine ((hcont.mono hKB).integrableOn_compact hK).of_forall_sdiff_eq_zero Metric.isOpen_ball.measurableSet ?_
  rintro w ⟨hwB, hwK⟩
  have hf0 : f (σ w) = 0 := by
    by_contra h
    exact hwK (Metric.mem_closedBall.2 (by
      simpa using (hN w hwB (hfN (subset_tsupport f h))).2))
  simp [hf0]

end

end GroundTheory.Heights₂.Heights
end
