module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle071
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle011
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularUFDLocalization
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle032
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle061
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle064
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric

namespace MaximalCountUnbranched

theorem analyticOnNhd_of_differentiableOn_pi {d : ℕ} {σ : Type} [Fintype σ] {U : Set (Fin d → ℂ)}
    {G : (Fin d → ℂ) → σ → ℂ} (hU : IsOpen U) (hG : DifferentiableOn ℂ G U) : AnalyticOnNhd ℂ G U := by
  intro y hy
  refine AnalyticAt.pi fun s => ?_
  have hs : DifferentiableOn ℂ (fun x => G x s) U := differentiableOn_pi.1 hG s
  refine analyticOnNhd_of_continuousOn_of_separately hU hs.continuousOn (fun z hz i => ?_) y hy
  have h1 : DifferentiableAt ℂ (fun x => G x s) (Function.update z i (z i)) := by
    rw [Function.update_eq_self]
    exact hs.differentiableAt (hU.mem_nhds hz)
  exact h1.comp (z i) (hasFDerivAt_update (𝕜 := ℂ) z (z i)).differentiableAt

theorem fibre_unique_near {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {d : ℕ}
    {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {N : ℕ} (hmaps : Set.MapsTo A Y D)
    (hopen : ∀ x ∈ Y, ∀ V ∈ 𝓝 x, A '' (Y ∩ V) ∈ 𝓝 (A x))
    (hle : ∀ y ∈ D, {x | x ∈ Y ∧ A x = y}.encard ≤ N)
    {z : σ → ℂ} (hz : z ∈ Y) (hzN : {x' | x' ∈ Y ∧ A x' = A z}.encard = N) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ W ∈ 𝓝 (A z), ∀ y ∈ W,
      {x' | x' ∈ Y ∧ A x' = y}.encard = N ∧ (∃ x' ∈ Y, A x' = y ∧ dist x' z < ε) ∧
      ∀ x₁ ∈ Y, ∀ x₂ ∈ Y, A x₁ = y → A x₂ = y → dist x₁ z < ε → dist x₂ z < ε → x₁ = x₂ := by
  have hSfin : {x' | x' ∈ Y ∧ A x' = A z}.Finite := Set.finite_of_encard_eq_coe hzN
  have hzS : z ∈ {x' | x' ∈ Y ∧ A x' = A z} := ⟨hz, rfl⟩
  have hsep : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p ∈ {x' | x' ∈ Y ∧ A x' = A z} ×ˢ {x' | x' ∈ Y ∧ A x' = A z},
      p.1 ≠ p.2 → 2 * ε < dist p.1 p.2 := by
    refine (eventually_all_finite (hSfin.prod hSfin)).2 fun p _ => ?_
    by_cases hp : p.1 = p.2
    · exact Eventually.of_forall fun _ h => absurd hp h
    · have hpos : 0 < dist p.1 p.2 / 2 := half_pos (dist_pos.2 hp)
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hpos)] with ε hε _
      linarith
  filter_upwards [hsep, self_mem_nhdsWithin] with ε hε hε0
  have hε0 : (0 : ℝ) < ε := hε0
  refine ⟨⋂ s ∈ {x' | x' ∈ Y ∧ A x' = A z}, A '' (Y ∩ ball s ε), (biInter_mem hSfin).2 fun s hs => ?_,
    fun y hy => ?_⟩
  · have := hopen s hs.1 (ball s ε) (ball_mem_nhds s hε0)
    rwa [hs.2] at this
  have hch : ∀ s ∈ {x' | x' ∈ Y ∧ A x' = A z}, ∃ p, p ∈ Y ∧ dist p s < ε ∧ A p = y := by
    intro s hs
    obtain ⟨p, ⟨hpY, hpb⟩, hpA⟩ := Set.mem_iInter₂.1 hy s hs
    exact ⟨p, hpY, mem_ball.1 hpb, hpA⟩
  choose! f hfY hfd hfA using hch
  have hinj : Set.InjOn f {x' | x' ∈ Y ∧ A x' = A z} := by
    intro s hs s' hs' he
    by_contra hne
    have h1 : 2 * ε < dist s s' := hε (s, s') ⟨hs, hs'⟩ hne
    have h2 : dist s s' ≤ dist (f s) s + dist (f s') s' := by
      calc dist s s' ≤ dist s (f s) + dist (f s) s' := dist_triangle _ _ _
        _ = dist (f s) s + dist (f s') s' := by rw [dist_comm s, he]
    linarith [hfd s hs, hfd s' hs']
  have hyD : y ∈ D := hfA z hzS ▸ hmaps (hfY z hzS)
  have hsub : f '' {x' | x' ∈ Y ∧ A x' = A z} ⊆ {x' | x' ∈ Y ∧ A x' = y} := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨hfY s hs, hfA s hs⟩
  have himg : (f '' {x' | x' ∈ Y ∧ A x' = A z}).encard = N := by rw [hinj.encard_image, hzN]
  have hFle := hle y hyD
  have hFeq : {x' | x' ∈ Y ∧ A x' = y}.encard = N :=
    le_antisymm hFle (himg ▸ Set.encard_le_encard hsub)
  have huniq : ∀ x₁ ∈ Y, A x₁ = y → dist x₁ z < ε → x₁ = f z := by
    intro x₁ hx₁ hA₁ hd₁
    by_contra hne
    have hnot : x₁ ∉ f '' {x' | x' ∈ Y ∧ A x' = A z} := by
      rintro ⟨s, hs, rfl⟩
      by_cases hsz : s = z
      · exact hne (hsz ▸ rfl)
      · have h1 : 2 * ε < dist s z := hε (s, z) ⟨hs, hzS⟩ hsz
        have h2 : dist s z ≤ dist (f s) s + dist (f s) z := by
          calc dist s z ≤ dist s (f s) + dist (f s) z := dist_triangle _ _ _
            _ = dist (f s) s + dist (f s) z := by rw [dist_comm s]
        linarith [hfd s hs]
    have hins : insert x₁ (f '' {x' | x' ∈ Y ∧ A x' = A z}) ⊆ {x' | x' ∈ Y ∧ A x' = y} :=
      Set.insert_subset ⟨hx₁, hA₁⟩ hsub
    have hc := Set.encard_le_encard hins
    rw [Set.encard_insert_of_notMem hnot, himg] at hc
    have hc' : ((N + 1 : ℕ) : ℕ∞) ≤ (N : ℕ∞) := by exact_mod_cast hc.trans hFle
    have : N + 1 ≤ N := by exact_mod_cast hc'
    omega
  refine ⟨hFeq, ⟨f z, hfY z hzS, hfA z hzS, hfd z hzS⟩, fun x₁ hx₁ x₂ hx₂ hA₁ hA₂ hd₁ hd₂ => ?_⟩
  rw [huniq x₁ hx₁ hA₁ hd₁, huniq x₂ hx₂ hA₂ hd₂]

theorem proof (hRE : RiemannExtensionAnalytic.Statement) : MaximalCountUnbranched.Statement := by
  intro σ _ Y d A D N _hD hmaps _hprop hopen hgen x hx hxN
  have key := fun (z : σ → ℂ) (hz : z ∈ Y) (hzN : {x' | x' ∈ Y ∧ A x' = A z}.encard = N) =>
    fibre_unique_near hmaps hopen hgen.1 hz hzN
  obtain ⟨ε, ⟨W₀, hW₀, hW₀p⟩, hε0⟩ := ((key x hx hxN).and self_mem_nhdsWithin).exists
  have hε0 : (0 : ℝ) < ε := hε0
  obtain ⟨U, g, hUo, hxU, _hUD, hg, hgnz, hgsec⟩ := hgen.2 (A x) (hmaps hx)
  have hOo : IsOpen (interior W₀ ∩ U) := isOpen_interior.inter hUo
  have hOW : ∀ y ∈ interior W₀ ∩ U, y ∈ W₀ := fun y hy => interior_subset hy.1
  have hex : ∀ y ∈ interior W₀ ∩ U, ∃ x' ∈ Y, A x' = y ∧ dist x' x < ε :=
    fun y hy => (hW₀p y (hOW y hy)).2.1
  choose! h hhY hhA hhd using hex
  have hu : ∀ y ∈ interior W₀ ∩ U, ∀ x' ∈ Y, A x' = y → dist x' x < ε → x' = h y :=
    fun y hy x' hx' hA hd =>
      (hW₀p y (hOW y hy)).2.2 x' hx' (h y) (hhY y hy) hA (hhA y hy) hd (hhd y hy)

  have hcont : ContinuousOn h (interior W₀ ∩ U) := by
    intro y₀ hy₀
    refine ContinuousAt.continuousWithinAt ?_
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro η hη
    have hzN : {x' | x' ∈ Y ∧ A x' = A (h y₀)}.encard = N := by
      rw [hhA y₀ hy₀]; exact (hW₀p y₀ (hOW y₀ hy₀)).1
    have hgap : 0 < ε - dist (h y₀) x := by linarith [hhd y₀ hy₀]
    have hsmall : ∀ᶠ e in 𝓝[>] (0 : ℝ), e < min η (ε - dist (h y₀) x) :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (lt_min hη hgap))
    obtain ⟨e, ⟨W₁, hW₁, hW₁p⟩, he⟩ := ((key (h y₀) (hhY y₀ hy₀) hzN).and hsmall).exists
    rw [hhA y₀ hy₀] at hW₁
    filter_upwards [hW₁, hOo.mem_nhds hy₀] with y hy1 hyO
    obtain ⟨x'', hx''Y, hx''A, hx''d⟩ := (hW₁p y hy1).2.1
    have hm1 := min_le_left η (ε - dist (h y₀) x)
    have hm2 := min_le_right η (ε - dist (h y₀) x)
    have hx''x : dist x'' x < ε := by
      have := dist_triangle x'' (h y₀) x
      linarith
    rw [← hu y hyO x'' hx''Y hx''A hx''x]
    linarith

  have hdiff : ∀ y₀ ∈ interior W₀ ∩ U, g y₀ ≠ 0 → DifferentiableAt ℂ h y₀ := by
    intro y₀ hy₀ hg₀
    obtain ⟨_, hsec⟩ := hgsec y₀ hy₀.2 hg₀
    obtain ⟨O₁, V₁, h₁, hO₁, _hV₁, hzV₁, han₁, hA₁, hYV₁⟩ := hsec (h y₀) (hhY y₀ hy₀) (hhA y₀ hy₀)
    have hz : h y₀ ∈ h₁ '' O₁ := hYV₁ ▸ ⟨hhY y₀ hy₀, hzV₁⟩
    obtain ⟨y₁, hy₁, hy₁e⟩ := hz
    have hy₁₀ : y₁ = y₀ := by rw [← hA₁ y₁ hy₁, hy₁e, hhA y₀ hy₀]
    rw [hy₁₀] at hy₁ hy₁e
    have hc₁ : ContinuousAt h₁ y₀ := (han₁ y₀ hy₁).continuousAt
    have hball : ball x ε ∈ 𝓝 (h₁ y₀) := by
      rw [hy₁e]; exact isOpen_ball.mem_nhds (mem_ball.2 (hhd y₀ hy₀))
    have heq : h₁ =ᶠ[𝓝 y₀] h := by
      filter_upwards [hc₁.preimage_mem_nhds hball, hO₁.mem_nhds hy₁, hOo.mem_nhds hy₀]
        with y hyb hyO₁ hyO
      have hyY : h₁ y ∈ Y := by
        have hmem : h₁ y ∈ h₁ '' O₁ := ⟨y, hyO₁, rfl⟩
        rw [← hYV₁] at hmem
        exact hmem.1
      exact hu y hyO (h₁ y) hyY (hA₁ y hyO₁) (mem_ball.1 hyb)
    exact (han₁ y₀ hy₁).differentiableAt.congr_of_eventuallyEq heq.symm

  have hgd : DifferentiableOn ℂ g (interior W₀ ∩ U) := hg.differentiableOn.mono fun y hy => hy.2
  have hgnz' : ∀ V : Set (Fin d → ℂ), IsOpen V → V ⊆ interior W₀ ∩ U → V.Nonempty → ∃ t ∈ V, g t ≠ 0 :=
    fun V hV hVO hVn => hgnz V hV (hVO.trans Set.inter_subset_right) hVn
  have hdense : interior W₀ ∩ U ⊆ closure ((interior W₀ ∩ U) ∩ {t | g t ≠ 0}) := by
    intro y hy
    rw [_root_.mem_closure_iff]
    intro o ho hyo
    obtain ⟨t, ht, hgt⟩ := hgnz' (o ∩ (interior W₀ ∩ U)) (ho.inter hOo) Set.inter_subset_right ⟨y, hyo, hy⟩
    exact ⟨t, ht.1, ht.2, hgt⟩
  have hcoord : ∀ j : σ, DifferentiableOn ℂ (fun y => h y j) (interior W₀ ∩ U) := by
    intro j
    have hdj : DifferentiableOn ℂ (fun y => h y j) ((interior W₀ ∩ U) ∩ {t | g t ≠ 0}) :=
      fun y hy => (differentiableAt_pi.1 (hdiff y hy.1 hy.2) j).differentiableWithinAt
    have hbj : ∀ τ ∈ interior W₀ ∩ U, ∃ M ∈ 𝓝 τ,
        Bornology.IsBounded ((fun y => h y j) '' (M ∩ (interior W₀ ∩ U) ∩ {t | g t ≠ 0})) := by
      intro τ _
      refine ⟨Set.univ, univ_mem, ?_⟩
      rw [isBounded_iff_forall_norm_le]
      refine ⟨‖x‖ + ε, ?_⟩
      rintro _ ⟨y, ⟨⟨_, hyO⟩, _⟩, rfl⟩
      calc ‖h y j‖ ≤ ‖h y‖ := norm_le_pi_norm (h y) j
        _ ≤ ‖x‖ + ε := norm_le_of_mem_closedBall (mem_closedBall.2 (hhd y hyO).le)
    obtain ⟨F, hF, hFe⟩ := hRE d (interior W₀ ∩ U) g (fun y => h y j) hOo hgd hgnz' hdj hbj
    have hEq : Set.EqOn F (fun y => h y j) (interior W₀ ∩ U) :=
      hFe.of_subset_closure hF.continuousOn (continuousOn_pi.1 hcont j) Set.inter_subset_left hdense
    exact hF.congr fun y hy => (hEq hy).symm
  have han : AnalyticOnNhd ℂ h (interior W₀ ∩ U) :=
    analyticOnNhd_of_differentiableOn_pi hOo (differentiableOn_pi.2 hcoord)
  refine ⟨interior W₀ ∩ U, ball x ε ∩ A ⁻¹' (interior W₀ ∩ U), h, hOo,
    isOpen_ball.inter (hOo.preimage A.continuous),
    ⟨mem_ball_self hε0, mem_interior_iff_mem_nhds.2 hW₀, hxU⟩, han, hhA, ?_⟩
  ext x'
  constructor
  · rintro ⟨hx'Y, hx'b, hx'O⟩
    exact ⟨A x', hx'O, (hu (A x') hx'O x' hx'Y rfl (mem_ball.1 hx'b)).symm⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hhY y hy, mem_ball.2 (hhd y hy), show A (h y) ∈ interior W₀ ∩ U from (hhA y hy).symm ▸ hy⟩

end MaximalCountUnbranched

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

theorem exists_ringKrullDim_quotient_eq_nat {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : J.IsPrime) :
    ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d := by
  have : J.IsPrime := hJ
  have hge : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) :=
    ringKrullDim_nonneg_of_nontrivial
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (n : WithBot ℕ∞) := by
    refine (ringKrullDim_quotient_le J).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card,
      Fintype.card_fin, zero_add]
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = x at hge hle
  induction x using WithBot.recBotCoe with
  | bot => exact absurd hge (by simp)
  | coe m =>
    induction m using ENat.recTopCoe with
    | top => exact absurd hle (by norm_cast)
    | coe d => exact ⟨d, rfl⟩

theorem analyticOnNhd_of_differentiableOn_fin {d : ℕ} {σ : Type} [Fintype σ] {U : Set (Fin d → ℂ)}
    {G : (Fin d → ℂ) → σ → ℂ} (hU : IsOpen U) (hG : DifferentiableOn ℂ G U) : AnalyticOnNhd ℂ G U := by
  intro y hy
  refine AnalyticAt.pi fun s => ?_
  have hs : DifferentiableOn ℂ (fun x => G x s) U :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) s).differentiable.comp_differentiableOn hG
  refine analyticOnNhd_of_continuousOn_of_separately hU hs.continuousOn (fun z hz i => ?_) y hy
  have h1 : DifferentiableAt ℂ (fun x => G x s) (Function.update z i (z i)) := by
    rw [Function.update_eq_self]
    exact hs.differentiableAt (hU.mem_nhds hz)
  exact h1.comp (z i) (hasFDerivAt_update (𝕜 := ℂ) z (z i)).differentiableAt

theorem RegularOffHypersurface.proof (hG : FrameGraphGeneric.Statement) : RegularOffHypersurface.Statement := by
  intro σ _ I hI
  set n := Fintype.card σ
  set e : σ ≃ Fin n := Fintype.equivFin σ
  set φ : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial σ ℂ := renameEquiv ℂ e.symm
  set J : Ideal (MvPolynomial (Fin n) ℂ) := I.comap φ
  have hJ : J.IsPrime := Ideal.IsPrime.comap _
  have hφ : ∀ (x : σ → ℂ) (q : MvPolynomial (Fin n) ℂ), eval x (φ q) = eval (x ∘ e.symm) q := fun x q => by
    simp [φ, eval_rename]
  obtain ⟨d, hd⟩ := exists_ringKrullDim_quotient_eq_nat J hJ
  let b := EuclideanSpace.basisFun (Fin n) ℂ
  obtain ⟨I₀, q, hcard, hqJ, hreg⟩ := hG n d J hJ hd b

  let T : (σ → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    ((EuclideanSpace.equiv (Fin n) ℂ).symm : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).comp
      (ContinuousLinearMap.pi fun i : Fin n => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) (e.symm i))
  let S : EuclideanSpace ℂ (Fin n) →L[ℂ] (σ → ℂ) :=
    (ContinuousLinearMap.pi fun s : σ => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (e s)).comp
      ((EuclideanSpace.equiv (Fin n) ℂ : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)))
  have hT : ∀ x i, T x i = x (e.symm i) := fun x i => rfl
  have hS : ∀ w s, S w s = w (e s) := fun w s => rfl
  have hST : ∀ x, S (T x) = x := fun x => funext fun s => by simp [hS, hT]
  have hTS : ∀ w, T (S w) = w := fun w => by ext i; simp [hS, hT]
  have hZ : ∀ x : σ → ℂ, x ∈ zeroSetIn I ↔ T x ∈ zeroSetEuc J := by
    intro x
    have hx : (fun i => T x i) = x ∘ e.symm := rfl
    simp only [zeroSetIn, zeroSetEuc, Set.mem_ofPred_eq, hx]
    constructor
    · intro h p hp
      rw [← hφ]
      exact h _ (Ideal.mem_comap.mp hp)
    · intro h p hp
      have := h (φ.symm p) (by simpa [J, Ideal.mem_comap] using hp)
      rwa [← hφ, AlgEquiv.apply_symm_apply] at this
  refine ⟨φ q, fun h => hqJ (Ideal.mem_comap.mpr h), ?_⟩
  intro z hz hzh
  obtain ⟨Ω, V, g, hΩ, hV, hzV, hg, hproj, hgraph⟩ :=
    hreg (T z) ((hZ z).mp hz) (by rwa [hφ] at hzh)
  let eI : I₀ ≃ Fin d := I₀.equivFinOfCardEq hcard
  let Ψ : (Fin d → ℂ) →L[ℂ] (I₀ → ℂ) :=
    ContinuousLinearMap.pi fun i : I₀ => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) (eI i)
  let A : (σ → ℂ) →L[ℂ] (Fin d → ℂ) :=
    ContinuousLinearMap.pi fun k : Fin d =>
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) (e.symm (eI.symm k))
  have hΨ : ∀ y i, Ψ y i = y (eI i) := fun y i => rfl
  have hA : ∀ x k, A x k = x (e.symm (eI.symm k)) := fun x k => rfl
  have hO : IsOpen (Ψ ⁻¹' Ω) := hΩ.preimage Ψ.continuous
  refine ⟨hz, d, A, Ψ ⁻¹' Ω, T ⁻¹' V, fun y => S (g (Ψ y)), hO, hV.preimage T.continuous, hzV, ?_, ?_, ?_⟩
  · exact analyticOnNhd_of_differentiableOn_fin hO (S.differentiable.comp_differentiableOn
      (hg.comp Ψ.differentiable.differentiableOn fun y hy => hy))
  · intro y hy
    ext k
    have h1 := congrFun (hproj (Ψ y) hy) (eI.symm k)
    simp only [GroundTheory.Heights₂.Heights.frameProj, b, EuclideanSpace.basisFun_inner] at h1
    show A (S (g (Ψ y))) k = y k
    rw [hA, hS, Equiv.apply_symm_apply, h1, hΨ, Equiv.apply_symm_apply]
  · ext x
    constructor
    · rintro ⟨hxZ, hxV⟩
      have hmem : T x ∈ zeroSetEuc J ∩ V := ⟨(hZ x).mp hxZ, hxV⟩
      rw [hgraph] at hmem
      obtain ⟨u, hu, hgu⟩ := hmem
      have hΨu : Ψ (fun k => u (eI.symm k)) = u := funext fun i => by simp [hΨ]
      refine ⟨fun k => u (eI.symm k), ?_, ?_⟩
      · show Ψ _ ∈ Ω
        rwa [hΨu]
      · simp only [hΨu, hgu, hST]
    · rintro ⟨y, hy, rfl⟩
      have hmem : g (Ψ y) ∈ zeroSetEuc J ∩ V := hgraph ▸ Set.mem_image_of_mem g hy
      refine ⟨(hZ _).mpr ?_, ?_⟩
      · rw [hTS]; exact hmem.1
      · show T (S (g (Ψ y))) ∈ V
        rw [hTS]; exact hmem.2

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem FormalFibresRegularPolynomial.proof (hJ : JacobianPrimeDerivations.Statement)
    (hE : DerivationAdicCompletion.Statement) (hC : AdicCompletionRegular.Statement)
    (hI : DerivationCotangentIndependent.Statement) (hQ : RegularQuotientIndependent.Statement) :
    FormalFibresRegularPolynomial.Statement := by
  intro k _ n M hM P _
  let B := MvPolynomial (Fin n) k
  let Bh := AdicCompletion M B
  let L := Localization.AtPrime P
  obtain ⟨h, f, D, s, hfp, hs, hsp, hdet⟩ := hJ k n (P.comap (algebraMap B Bh)) (Ideal.comap_isPrime _ _)
  choose D' hD' using fun j => hE B M (D j)
  have : IsRegularLocalRing Bh := hC B inferInstance M inferInstance
  have : IsRegularLocalRing L := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.localization_atPrime P
  have hdet' : (Matrix.of fun i j => D' j (algebraMap B Bh (f i))).det ∉ P := by
    have hm : (Matrix.of fun i j => D' j (algebraMap B Bh (f i))) =
        (algebraMap B Bh).mapMatrix (Matrix.of fun i j => D j (f i)) := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
      exact hD' j (f i)
    rw [hm, ← RingHom.map_det]
    exact hdet
  have hmem : ∀ i, algebraMap Bh L (algebraMap B Bh (f i)) ∈ maximalIdeal L := fun i =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff L P _).mpr (hfp i)
  have hreg := hQ L h _ hmem (hI Bh P h D' (fun i => algebraMap B Bh (f i)) hfp hdet')
  have heq : Ideal.span (Set.range fun i => algebraMap Bh L (algebraMap B Bh (f i))) =
      Ideal.map (algebraMap Bh L) (Ideal.map (algebraMap B Bh) (P.comap (algebraMap B Bh))) := by
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (hfp i))
    · rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro x hx
      have hu : IsUnit (algebraMap Bh L (algebraMap B Bh s)) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff L P _).mpr hs
      have hsx := Ideal.mem_map_of_mem ((algebraMap Bh L).comp (algebraMap B Bh)) (hsp x hx)
      rw [Ideal.map_span, ← Set.range_comp, map_mul] at hsx
      exact (Ideal.unit_mul_mem_iff_mem _ hu).mp hsx
  exact IsRegularLocalRing.of_ringEquiv (Ideal.quotEquivOfEq heq)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

theorem dim_eq_of_height_add {h : ℕ∞} {x : WithBot ℕ∞} {e : ℕ} (h1 : x + 1 ≤ ((e + 1 : ℕ) : WithBot ℕ∞))
    (hh : h ≤ 1) (hsum : (h : WithBot ℕ∞) + x = ((e + 1 : ℕ) : WithBot ℕ∞)) : x = ((e : ℕ) : WithBot ℕ∞) := by
  cases x using WithBot.recBotCoe with
  | bot => rw [WithBot.add_bot] at hsum; exact absurd hsum (WithBot.bot_ne_natCast _)
  | coe y =>
    cases y using ENat.recTopCoe with
    | top =>
      have h1' : (((⊤ : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((e + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := h1
      rw [WithBot.coe_le_coe, top_add, top_le_iff] at h1'
      exact absurd h1' (ENat.natCast_ne_top _)
    | coe y =>
      cases h using ENat.recTopCoe with
      | top => simp at hh
      | coe h =>
        have a1 : h + y = e + 1 := by exact_mod_cast hsum
        have a2 : h ≤ 1 := by exact_mod_cast hh
        have a3 : y + 1 ≤ e + 1 := by exact_mod_cast h1
        have : y = e := by omega
        subst this; rfl

theorem ringKrullDim_component {n d : ℕ} {J W : Ideal (MvPolynomial (Fin n) ℂ)} [J.IsPrime]
    {s : MvPolynomial (Fin n) ℂ} (hs : s ∉ J) (hW : W ∈ (J ⊔ Ideal.span {s}).minimalPrimes)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((d + 1 : ℕ) : WithBot ℕ∞)) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = ((d : ℕ) : WithBot ℕ∞) := by
  have _ : W.IsPrime := hW.1.1
  have hJW : J ≤ W := le_sup_left.trans hW.1.2
  have hsW : s ∈ W := (le_sup_right.trans hW.1.2) (Ideal.mem_span_singleton_self _)
  have _ : Algebra.FiniteType ℂ (MvPolynomial (Fin n) ℂ ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ J) (Ideal.Quotient.mkₐ_surjective ℂ J)
  set W' : Ideal (MvPolynomial (Fin n) ℂ ⧸ J) := W.map (Ideal.Quotient.mk J)
  have _ : W'.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hW'ne : W' ≠ ⊥ := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp (by
    have : Ideal.Quotient.mk J s ∈ W' := Ideal.mem_map_of_mem _ hsW
    rwa [h, Ideal.mem_bot] at this))
  have hquot : ringKrullDim ((MvPolynomial (Fin n) ℂ ⧸ J) ⧸ W') = ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hJW)
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient ℂ W'
  have hdrop := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le W' hW'ne
  rw [hquot, hdim] at hform hdrop
  exact dim_eq_of_height_add hdrop (Ideal.map_height_le_one_of_mem_minimalPrimes hW) hform

theorem SliceMultGeneral.proof (hC : CMGeneralPoint.Statement) (hT : TransverseSliceGeneral.Statement)
    (hL : LengthTransverseSlice.Statement) : SliceMultGeneral.Statement := by
  intro n d J W u hJ hdim hu hW
  have hWp : W.IsPrime := hW.1.1
  have hdW := ringKrullDim_component hu hW hdim
  obtain ⟨f₁, hf₁W, hf₁⟩ := hC n _ W hW
  obtain ⟨f₂, hf₂W, hf₂⟩ := hT n d W hWp hdW
  refine ⟨f₁ * f₂, fun h => (hWp.mem_or_mem h).elim hf₁W hf₂W, fun q hq hqf => ?_⟩
  rw [map_mul, mul_ne_zero_iff] at hqf
  obtain ⟨hone, hcm⟩ := hf₁ q hq hqf.1
  obtain ⟨hO, hD⟩ := hf₂ q hq hqf.2
  refine ⟨_, hO, hD, fun L hL' => ?_⟩
  have hsl : sliceIdeal J L q ⊔ Ideal.span {linForm u} = sliceIdeal (J ⊔ Ideal.span {linForm u}) L q := by
    simp only [sliceIdeal, sup_right_comm]
  rw [hsl]
  exact hL n d _ W q L hW hdW hq hone hcm hL'

end GroundTheory.Heights₂.Heights
end
