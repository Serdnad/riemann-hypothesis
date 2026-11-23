module

import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle056
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle015
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle067
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle048
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle068
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle038
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle059
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle006
public import Mathlib.Analysis.Analytic.Basic
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle071
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
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
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

theorem isAnalyticNear_zeroSetIn {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) :
    IsAnalyticNear (zeroSetIn I) w := by
  apply GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn_isAnalyticNear <;> assumption

theorem analyticOnNhd_of_differentiableOn_scalar_fin {d : ℕ} {U : Set (Fin d → ℂ)} {F : (Fin d → ℂ) → ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) : AnalyticOnNhd ℂ F U := by
  refine analyticOnNhd_of_continuousOn_of_separately hU hF.continuousOn (fun z hz i => ?_)
  have h1 : DifferentiableAt ℂ F (Function.update z i (z i)) := by
    rw [Function.update_eq_self]
    exact hF.differentiableAt (hU.mem_nhds hz)
  exact h1.comp (z i) (hasFDerivAt_update (𝕜 := ℂ) z (z i)).differentiableAt

theorem germIrreducibleAt_zeroSetIn_of_integrallyClosed (hic : NormalGermIntegrallyClosed.Statement)
    {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (hI : I.IsPrime)
    (hn : IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I)) (hw : w ∈ zeroSetIn I) :
    GermIrreducibleAt (zeroSetIn I) w := by
  refine ⟨hw, fun f g hf hg hfg => ?_⟩
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hfne, hgne⟩ := hcon
  set X := zeroSetIn I with hX
  set N : Set (σ → ℂ) :=
    ({z | AnalyticAt ℂ f z} ∩ {z | AnalyticAt ℂ g z}) ∩ interior {z | z ∈ X → f z * g z = 0} with hNdef
  have hNo : IsOpen N := ((isOpen_analyticAt ℂ f).inter (isOpen_analyticAt ℂ g)).inter isOpen_interior
  have hwN : w ∈ N := ⟨⟨hf, hg⟩, mem_interior_iff_mem_nhds.mpr hfg⟩
  have hfd : DifferentiableOn ℂ f N := fun z hz => hz.1.1.differentiableAt.differentiableWithinAt
  have hgd : DifferentiableOn ℂ g N := fun z hz => hz.1.2.differentiableAt.differentiableWithinAt
  have hfgN : ∀ z ∈ X ∩ N, f z * g z = 0 := fun z hz => interior_subset hz.2.2 hz.1
  have hGne : ¬ ∀ᶠ z in 𝓝 w, z ∈ X → (f + g) z = 0 := by
    intro hev
    apply hfne
    filter_upwards [hev, hfg] with z h1 h2 hz
    have hs : f z + g z = 0 := h1 hz
    have hp : f z * g z = 0 := h2 hz
    have hff : f z * f z = 0 := by linear_combination f z * hs - hp
    exact mul_self_eq_zero.mp hff
  have ha : ∀ j, DifferentiableOn ℂ ((![0, -1] : Fin 2 → (σ → ℂ) → ℂ) j) N := by
    intro j
    fin_cases j
    · exact differentiableOn_const (0 : ℂ)
    · exact differentiableOn_const (-1 : ℂ)
  obtain ⟨V, hV, hwV, H, hH, hfH⟩ := hic σ I w N f (f + g) 2 ![0, -1] hI hn hw hNo hwN hfd (hfd.add hgd)
    ha hGne (by
      intro z hz
      have hp := hfgN z hz.1
      simp [Fin.sum_univ_two]
      linear_combination -hp)
  have hHc : ContinuousAt H w := (hH.differentiableAt (hV.mem_nhds hwV)).continuousAt
  have hev : ∀ᶠ z in 𝓝 w, z ∈ V ∧ (z ∈ X → f z * g z = 0) := (show ∀ᶠ z in 𝓝 w, z ∈ V from hV.mem_nhds hwV).and hfg
  rw [Filter.not_eventually] at hfne hgne
  have h1 : H w = 1 := by
    by_contra hne
    obtain ⟨z, hz, hzH⟩ := (hfne.and_eventually (hev.and (hHc.eventually_ne hne))).exists
    push Not at hz
    have hg0 : g z = 0 := (mul_eq_zero.mp (hzH.1.2 hz.1)).resolve_left hz.2
    have hfz := hfH z ⟨hz.1, hzH.1.1⟩
    simp only [Pi.add_apply, hg0, add_zero] at hfz
    exact hzH.2 (mul_left_cancel₀ hz.2 (hfz.symm.trans (mul_one _).symm))
  have h0 : H w = 0 := by
    by_contra hne
    obtain ⟨z, hz, hzH⟩ := (hgne.and_eventually (hev.and (hHc.eventually_ne hne))).exists
    push Not at hz
    have hf0 : f z = 0 := (mul_eq_zero.mp (hzH.1.2 hz.1)).resolve_right hz.2
    have hfz := hfH z ⟨hz.1, hzH.1.1⟩
    simp only [Pi.add_apply, hf0, zero_add] at hfz
    exact hzH.2 ((mul_eq_zero.mp hfz.symm).resolve_left hz.2)
  exact one_ne_zero (h1.symm.trans h0)

theorem NormalZerosNowhereDense.proof (hic : NormalGermIntegrallyClosed.Statement)
    (hconn : IrreducibleGermRegularConnected.Statement) (hdense : RegularLocusDense.Statement) :
    NormalZerosNowhereDense.Statement := by
  intro σ _ I w N G hI hn hw hN hwN hG hne
  have han := isAnalyticNear_zeroSetIn I w
  have hirr := germIrreducibleAt_zeroSetIn_of_integrallyClosed hic I w hI hn hw
  set X := zeroSetIn I with hX
  obtain ⟨N₀, hN₀, hwN₀, hd⟩ := hdense σ X w han
  obtain ⟨B, hB, hwB, hBU, hpc⟩ :=
    hconn σ X w han hirr (N ∩ N₀) (Filter.inter_mem (hN.mem_nhds hwN) (hN₀.mem_nhds hwN₀))
  have hBN : B ⊆ N := hBU.trans Set.inter_subset_left
  have hdB : X ∩ B ⊆ closure (regLocus (X ∩ B)) := hd B hB (hBU.trans Set.inter_subset_right)
  refine ⟨B, hB, hwB, hBN, ?_⟩
  intro z hz V hV
  by_contra hall
  push Not at hall
  set R := regLocus (X ∩ B) with hR
  set T : Set (σ → ℂ) := {y | y ∈ X → G y = 0} with hT

  have hloc : ∀ x ∈ R, ∃ M : Set (σ → ℂ), IsOpen M ∧ x ∈ M ∧ ((∃ p ∈ X ∩ M, T ∈ 𝓝 p) → M ⊆ T) := by
    intro x hx
    have hx' : IsRegularPointOf (X ∩ B) x := hx
    obtain ⟨hxXB, d, A, O, W, g, hO, hW, hxW, hg, hAg, hYW⟩ := hx'
    obtain ⟨y₀, hy₀O, hgy₀⟩ : x ∈ g '' O := by rw [← hYW]; exact ⟨hxXB, hxW⟩
    obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO y₀ hy₀O
    have hgO : ∀ y ∈ O, g y ∈ X ∩ B := by
      intro y hy
      have hy' : g y ∈ (X ∩ B) ∩ W := by rw [hYW]; exact Set.mem_image_of_mem g hy
      exact hy'.1
    have hxA : A x ∈ Metric.ball y₀ r := by
      rw [← hgy₀, hAg y₀ hy₀O]
      exact Metric.mem_ball_self hr
    refine ⟨W ∩ B ∩ A ⁻¹' Metric.ball y₀ r,
      (hW.inter hB).inter (Metric.isOpen_ball.preimage A.continuous), ⟨⟨hxW, hxXB.2⟩, hxA⟩, ?_⟩
    have hcov : ∀ p ∈ X ∩ (W ∩ B ∩ A ⁻¹' Metric.ball y₀ r), ∃ y ∈ Metric.ball y₀ r, g y = p := by
      rintro p ⟨hpX, ⟨hpW, hpB⟩, hpA⟩
      obtain ⟨y, hyO, rfl⟩ : p ∈ g '' O := by rw [← hYW]; exact ⟨⟨hpX, hpB⟩, hpW⟩
      refine ⟨y, ?_, rfl⟩
      have hpA' : A (g y) ∈ Metric.ball y₀ r := hpA
      rwa [hAg y hyO] at hpA'
    have hF : AnalyticOnNhd ℂ (fun y => G (g y)) (Metric.ball y₀ r) := by
      refine analyticOnNhd_of_differentiableOn_scalar_fin Metric.isOpen_ball (fun y hy => ?_)
      have hyO := hrO hy
      exact ((hG.differentiableAt (hN.mem_nhds (hBN (hgO y hyO).2))).comp y
        (hg y hyO).differentiableAt).differentiableWithinAt
    rintro ⟨p, hpXM, hpT⟩
    obtain ⟨y₁, hy₁, rfl⟩ := hcov p hpXM
    have hev : (fun y => G (g y)) =ᶠ[𝓝 y₁] 0 := by
      filter_upwards [(hg y₁ (hrO hy₁)).continuousAt.preimage_mem_nhds hpT,
        Metric.isOpen_ball.mem_nhds hy₁] with y hyT hyb
      exact hyT (hgO y (hrO hyb)).1
    have hzero := hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball y₀ r).isPreconnected hy₁ hev
    intro q hq hqX
    obtain ⟨y, hy, rfl⟩ := hcov q ⟨hqX, hq⟩
    exact hzero hy
  choose! M hMo hxM hMT using hloc

  have hallR : ∀ x ∈ R, T ∈ 𝓝 x := by
    obtain ⟨x₀, hx₀V, hx₀R⟩ := mem_closure_iff_nhds.mp (hdB hz) (interior V) (interior_mem_nhds.mpr hV)
    have hx₀T : T ∈ 𝓝 x₀ :=
      Filter.mem_of_superset (isOpen_interior.mem_nhds hx₀V) (fun y hy hyX => hall y ⟨hyX, interior_subset hy⟩)
    by_contra hbad
    push Not at hbad
    obtain ⟨x₁, hx₁R, hx₁T⟩ := hbad
    have hu : IsOpen (⋃ x ∈ {x | x ∈ R ∧ T ∈ 𝓝 x}, M x) := isOpen_biUnion fun x hx => hMo x hx.1
    have hv : IsOpen (⋃ x ∈ {x | x ∈ R ∧ T ∉ 𝓝 x}, M x) := isOpen_biUnion fun x hx => hMo x hx.1
    have hcover : R ⊆ (⋃ x ∈ {x | x ∈ R ∧ T ∈ 𝓝 x}, M x) ∪ (⋃ x ∈ {x | x ∈ R ∧ T ∉ 𝓝 x}, M x) := by
      intro x hx
      by_cases h : T ∈ 𝓝 x
      · exact Or.inl (Set.mem_biUnion (x := x) ⟨hx, h⟩ (hxM x hx))
      · exact Or.inr (Set.mem_biUnion (x := x) ⟨hx, h⟩ (hxM x hx))
    obtain ⟨q, hqR, hqu, hqv⟩ := hpc _ _ hu hv hcover
      ⟨x₀, hx₀R, Set.mem_biUnion (x := x₀) ⟨hx₀R, hx₀T⟩ (hxM x₀ hx₀R)⟩
      ⟨x₁, hx₁R, Set.mem_biUnion (x := x₁) ⟨hx₁R, hx₁T⟩ (hxM x₁ hx₁R)⟩
    obtain ⟨a, ⟨haR, haT⟩, hqa⟩ := Set.mem_iUnion₂.mp hqu
    obtain ⟨b, ⟨hbR, hbT⟩, hqb⟩ := Set.mem_iUnion₂.mp hqv
    have hqX : q ∈ X := (regLocus_subset _ hqR).1
    have hMa : M a ⊆ T := hMT a haR ⟨a, ⟨(regLocus_subset _ haR).1, hxM a haR⟩, haT⟩
    have hqT : T ∈ 𝓝 q := Filter.mem_of_superset ((hMo a haR).mem_nhds hqa) hMa
    have hMb : M b ⊆ T := hMT b hbR ⟨q, ⟨hqX, hqb⟩, hqT⟩
    exact hbT (Filter.mem_of_superset ((hMo b hbR).mem_nhds (hxM b hbR)) hMb)

  have hzeroB : ∀ y ∈ X ∩ B, G y = 0 := by
    intro y hy
    by_contra hGy
    have hc : ContinuousAt G y := (hG.differentiableAt (hN.mem_nhds (hBN hy.2))).continuousAt
    obtain ⟨x, hxG, hxR⟩ := mem_closure_iff_nhds.mp (hdB hy) _ (hc.eventually_ne hGy)
    exact hxG (mem_of_mem_nhds (hallR x hxR) (regLocus_subset _ hxR).1)
  exact hne (Filter.mem_of_superset (hB.mem_nhds hwB) fun y hyB hyX => hzeroB y ⟨hyX, hyB⟩)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets

noncomputable section

namespace DivisorBranches

theorem quotient_inf_dim_lt {R : Type*} [CommRing R] {I₁ I₂ : Ideal R} {d : ℕ}
    (h₁ : ringKrullDim (R ⧸ I₁) < (d : ℕ)) (h₂ : ringKrullDim (R ⧸ I₂) < (d : ℕ)) :
    ringKrullDim (R ⧸ (I₁ ⊓ I₂)) < (d : ℕ) := by
  apply _root_.GroundTheory.Heights₂.Heights.DivisorGeneralPointBranches.quotient_inf_dim_lt <;> assumption

theorem not_mem_zeroSet_of_le {n : ℕ} {I I' : Ideal (MvPolynomial (Fin n) ℂ)} (hle : I ≤ I')
    {q : Fin n → ℂ} (hq : q ∉ zeroSet I) : q ∉ zeroSet I' :=
  fun h => hq fun f hf => h f (hle hf)

theorem proof (hModel : IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.Statement)
    (hReg : DivisorRegularGeneric.Statement) (hChart : NormalDivisorChartGeneric.Statement)
    (hDouble : NormalDoublePointsGeneric.Statement) (hGood : DivisorGoodPointBranches.Statement) :
    DivisorBranches.Statement := by
  intro n d J u hJ hdim hu
  obtain ⟨M⟩ := hModel n J hJ
  obtain ⟨I₁, hle₁, hdim₁, hI₁⟩ := hReg n d J u hJ hdim hu
  obtain ⟨I₂, hle₂, hdim₂, hI₂⟩ := hChart n d J u M hJ hdim hu
  obtain ⟨I₃, hle₃, hdim₃, hI₃⟩ := hDouble n d J u M hJ hdim hu
  refine ⟨I₁ ⊓ I₂ ⊓ I₃, le_inf (le_inf hle₁ hle₂) hle₃,
    quotient_inf_dim_lt (quotient_inf_dim_lt hdim₁ hdim₂) hdim₃, ?_⟩
  intro q hqJ hqu hqI
  exact hGood n d J u M q hJ hdim hu hqJ hqu
    (hI₁ q hqJ hqu (not_mem_zeroSet_of_le (inf_le_left.trans inf_le_left) hqI))
    (hI₂ q hqJ hqu (not_mem_zeroSet_of_le (inf_le_left.trans inf_le_right) hqI))
    (hI₃ q hqJ hqu (not_mem_zeroSet_of_le inf_le_right hqI))

end DivisorBranches

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem SeparateWeierstrassDivision.proof (h : WeierstrassPolynomialDivision.Statement) :
    SeparateWeierstrassDivision.Statement := by
  suffices H : ∀ (N : ℕ) (σ : Type) [Fintype σ] [DecidableEq σ], Fintype.card σ = N →
      ∀ (d : ℕ) (y₀ : Fin d → ℂ) (u₀ : σ → ℂ) (n : σ → ℕ)
        (b : (m : σ) → Fin (n m) → (Fin d → ℂ) → ℂ) (f : (Fin d → ℂ) × (σ → ℂ) → ℂ),
        (∀ m j, AnalyticAt ℂ (b m j) y₀) →
        (∀ m (T : ℂ), T ^ n m + ∑ j, b m j y₀ * T ^ (j : ℕ) = (T - u₀ m) ^ n m) →
        AnalyticAt ℂ f (y₀, u₀) →
        ∃ (v : σ → (Fin d → ℂ) × (σ → ℂ) → ℂ) (r : ((m : σ) → Fin (n m)) → (Fin d → ℂ) → ℂ),
          (∀ m, AnalyticAt ℂ (v m) (y₀, u₀)) ∧ (∀ α, AnalyticAt ℂ (r α) y₀) ∧
          ∀ᶠ x in 𝓝 (y₀, u₀),
            f x = ∑ m, v m x * (x.2 m ^ n m + ∑ j, b m j x.1 * x.2 m ^ (j : ℕ)) +
              ∑ α, r α x.1 * ∏ m, x.2 m ^ (α m : ℕ) by
    intro σ _ _ d y₀ u₀ n b f hb hG hf
    exact H _ σ rfl d y₀ u₀ n b f hb hG hf
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro σ _ _ hN d y₀ u₀ n b f hb hG hf
  rcases isEmpty_or_nonempty σ with hσ | ⟨⟨k⟩⟩
  ·
    refine ⟨fun _ _ => 0, fun _ y => f (y, u₀), fun _ => analyticAt_const,
      fun _ => hf.comp_of_eq (analyticAt_id.prod analyticAt_const) rfl, Eventually.of_forall fun x => ?_⟩
    have hx : x = (x.1, u₀) := Prod.ext rfl (Subsingleton.elim _ _)
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Finset.prod_empty, mul_one, zero_add,
      Fintype.sum_unique]
    rw [← hx]
  · obtain ⟨q, e, hq, he, hev⟩ :=
      weierstrassDivision_in_coordinate h k d y₀ u₀ (n k) (b k) f (hb k) (hG k) hf
    have hlt : Fintype.card {m // m ≠ k} < N :=
      hN ▸ Fintype.card_subtype_lt (p := fun m => m ≠ k) (x := k) (by simp)
    have IH := fun i => ih _ hlt {m // m ≠ k} rfl d y₀ (fun m => u₀ m) (fun m => n m)
      (fun m => b m) (e i) (fun m j => hb m j) (fun m T => hG m T) (he i)
    choose V R hV hR hVR using IH
    have hπ : AnalyticAt ℂ (fun x : (Fin d → ℂ) × (σ → ℂ) => (x.1, fun m : {m // m ≠ k} => x.2 m)) (y₀, u₀) :=
      analyticAt_fst.prod (AnalyticAt.pi (f := fun (m : {m // m ≠ k}) (x : (Fin d → ℂ) × (σ → ℂ)) => x.2 m)
        fun m => (analyticAt_coord _ _).comp analyticAt_snd)
    refine ⟨fun m x => if hm : m = k then q x else
        ∑ i, V i ⟨m, hm⟩ (x.1, fun m' => x.2 m') * x.2 k ^ (i : ℕ),
      fun α y => R (α k) (fun m' => α m') y, fun m => ?_, fun α => hR _ _, ?_⟩
    · by_cases hm : m = k
      · simpa [hm] using hq
      · simp only [hm, dite_false]
        exact Finset.analyticAt_fun_sum _ fun i _ =>
          ((hV i ⟨m, hm⟩).comp_of_eq hπ rfl).fun_mul
            (((analyticAt_coord k _).comp analyticAt_snd).fun_pow _)
    · have hT : Tendsto (fun x : (Fin d → ℂ) × (σ → ℂ) => (x.1, fun m' : {m // m ≠ k} => x.2 m'))
          (𝓝 (y₀, u₀)) (𝓝 (y₀, fun m' => u₀ m')) := hπ.continuousAt.tendsto
      filter_upwards [hev, hT.eventually (Filter.eventually_all.2 hVR)] with x hx hx'
      rw [hx, Fintype.sum_eq_add_sum_subtype_ne _ k,
        ← (Equiv.piSplitAt k (fun m => Fin (n m))).symm.sum_comp, Fintype.sum_prod_type]
      have hne : ∀ m : {m // m ≠ k}, ¬ ((m : σ) = k) := fun m => m.2
      simp_rw [Fintype.prod_eq_mul_prod_subtype_ne _ k]
      simp only [Equiv.piSplitAt_symm_apply, dite_true, hne, dite_false, Subtype.coe_eta, hx']
      simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
      rw [add_assoc]
      congr 1
      congr 1
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => by ring
      · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun α _ => by ring
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology

namespace InjectiveHolomorphicInverse

theorem analyticAt_of_differentiableOn {k : ℕ} {U : Set (Fin k → ℂ)} {f : (Fin k → ℂ) → Fin k → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {x : Fin k → ℂ} (hx : x ∈ U) : AnalyticAt ℂ f x := by
  refine AnalyticAt.pi fun i => ?_
  refine analyticOnNhd_of_continuousOn_of_separately hU
    ((continuous_apply i).comp_continuousOn hf.continuousOn) (fun z hz j => ?_) x hx
  have hfz : DifferentiableAt ℂ (fun w => f w i) z :=
    differentiableAt_pi.mp (hf.differentiableAt (hU.mem_nhds hz)) i
  have hu : DifferentiableAt ℂ (Function.update z j) (z j) :=
    (hasFDerivAt_update z (z j)).differentiableAt
  have hfz' : DifferentiableAt ℂ (fun w => f w i) (Function.update z j (z j)) := by
    rwa [Function.update_eq_self]
  exact hfz'.comp (z j) hu

theorem exists_equiv (hJ : InjectiveHolomorphicJacobianNeZero.Statement) {k : ℕ} {U : Set (Fin k → ℂ)}
    {f : (Fin k → ℂ) → Fin k → ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : Set.InjOn f U)
    {x : Fin k → ℂ} (hx : x ∈ U) :
    ∃ e : (Fin k → ℂ) ≃L[ℂ] (Fin k → ℂ), HasStrictFDerivAt f (e : (Fin k → ℂ) →L[ℂ] Fin k → ℂ) x := by
  have hdet := hJ k U f hU hf hinj x hx
  refine ⟨(LinearMap.equivOfDetNeZero _ hdet).toContinuousLinearEquiv, ?_⟩
  have he : ((LinearMap.equivOfDetNeZero _ hdet).toContinuousLinearEquiv :
      (Fin k → ℂ) →L[ℂ] Fin k → ℂ) = fderiv ℂ f x := by
    ext1 v
    rfl
  rw [he]
  exact (analyticAt_of_differentiableOn hU hf hx).hasStrictFDerivAt

theorem proof (hJ : InjectiveHolomorphicJacobianNeZero.Statement) : InjectiveHolomorphicInverse.Statement := by
  intro k U f hU hf hinj
  have hleft : ∀ z ∈ U, Function.invFunOn f U (f z) = z := fun z hz =>
    hinj (Function.invFunOn_mem ⟨z, hz, rfl⟩) hz (Function.invFunOn_eq ⟨z, hz, rfl⟩)
  refine ⟨?_, Function.invFunOn f U, ?_, hleft⟩
  · rw [isOpen_iff_mem_nhds]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨e, he⟩ := exists_equiv hJ hU hf hinj hx
    rw [← he.map_nhds_eq_of_equiv]
    exact Filter.image_mem_map (hU.mem_nhds hx)
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨e, he⟩ := exists_equiv hJ hU hf hinj hx
    refine (he.to_local_left_inverse ?_).differentiableAt.differentiableWithinAt
    filter_upwards [hU.mem_nhds hx] with z hz
    exact hleft z hz

end InjectiveHolomorphicInverse

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter

theorem NonIsolatedFibreCurve.analyticOnNhd_of_differentiableOn {k : ℕ} {O : Set (Fin k → ℂ)}
    {g : (Fin k → ℂ) → ℂ} (hO : IsOpen O) (hg : DifferentiableOn ℂ g O) : AnalyticOnNhd ℂ g O := by
  refine analyticOnNhd_of_continuousOn_of_separately hO hg.continuousOn fun z hz i => ?_
  have h1 : DifferentiableAt ℂ g (Function.update z i (z i)) := by
    rw [Function.update_eq_self]
    exact hg.differentiableAt (hO.mem_nhds hz)
  exact h1.comp (z i) (hasFDerivAt_update z (z i)).differentiableAt

theorem NonIsolatedFibreCurve.proof (hComp : AnalyticGermComponents.Statement)
    (hCurve : IrreducibleGermCurve.Statement) : NonIsolatedFibreCurve.Statement := by
  intro k m U f p hU hf hp hacc
  set Z : Set (Fin k → ℂ) := {v | v ∈ U ∧ f v = f p} with hZ
  have hZan : IsAnalyticNear Z p := by
    refine ⟨U, m, fun i v => f v i - f p i, hU, hp, fun i => ?_, ?_⟩
    · exact analyticOnNhd_of_differentiableOn hU ((differentiableOn_pi.1 hf i).sub_const _)
    · ext v
      simp only [hZ, Set.mem_inter_iff, Set.mem_ofPred_eq, sub_eq_zero, funext_iff]
      tauto
  obtain ⟨n, Y, hY, W, hW, hZW⟩ := hComp (Fin k) Z p hZan ⟨hp, rfl⟩

  have hfreq : ∃ᶠ y in 𝓝 p, y ≠ p ∧ y ∈ ⋃ i, Y i := by
    have h := accPt_iff_frequently.1 hacc
    refine (h.and_eventually hW).mono fun y ⟨⟨hne, hyZ⟩, hyW⟩ => ⟨hne, ?_⟩
    have : y ∈ Z ∩ W := ⟨hyZ, hyW⟩
    rw [hZW] at this
    exact this.1
  obtain ⟨i, hi⟩ : ∃ i, AccPt p (𝓟 (Y i)) := by
    by_contra hno
    push Not at hno
    have hev : ∀ᶠ y in 𝓝 p, ∀ i, ¬ (y ≠ p ∧ y ∈ Y i) := by
      refine eventually_all.2 fun i => ?_
      have := hno i
      rw [accPt_iff_frequently, Filter.not_frequently] at this
      exact this
    obtain ⟨y, ⟨hne, hyU⟩, hy⟩ := (hfreq.and_eventually hev).exists
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hyU
    exact hy j ⟨hne, hj⟩
  obtain ⟨r, hr, γ, hγd, hγi, hγ0, hγm⟩ := hCurve (Fin k) (Y i) p (hY i).1 (hY i).2 hi

  have hcont : ContinuousAt γ 0 := (hγd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).continuousAt
  have hpre : γ ⁻¹' W ∈ 𝓝 (0 : ℂ) := hcont.preimage_mem_nhds (by rwa [hγ0])
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.1 hpre
  have hsub : ball (0 : ℂ) (min r ε) ⊆ ball 0 r := ball_subset_ball (min_le_left _ _)
  refine ⟨min r ε, lt_min hr hε, γ, hγd.mono hsub, hγi.mono hsub, hγ0, fun τ hτ => ?_⟩
  have hτW : γ τ ∈ W := hεW (ball_subset_ball (min_le_right _ _) hτ)
  have : γ τ ∈ (⋃ j, Y j) ∩ W := ⟨Set.mem_iUnion.2 ⟨i, hγm (hsub hτ)⟩, hτW⟩
  rw [← hZW] at this
  exact this.1

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
