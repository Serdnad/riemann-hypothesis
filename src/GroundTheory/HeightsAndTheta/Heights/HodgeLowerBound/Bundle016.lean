module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices.InstFintypeFlIdx
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Assembly
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlag
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle011
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle002
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm.M (FinHolAtlas)

theorem analyticAt_holoOn_comp_chartSymm {e m : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas e X}
    {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hψ : ReciprocityTheory.AnForm.M.IsCompatChart A ψ) {V : Set X}
    {F : X → ℂ} (hF : A.HoloOn V F) {g : (Fin m → ℂ) → Fin e → ℂ} {y : Fin m → ℂ} (hg : AnalyticAt ℂ g y)
    (hgy : g y ∈ ψ.target) (hV : ψ.symm (g y) ∈ V) :
    AnalyticAt ℂ (fun y' => F (ψ.symm (g y'))) y := by
  obtain ⟨i, hi⟩ := A.cover (ψ.symm (g y))
  have hτ : AnalyticAt ℂ (A.chart i ∘ ψ.symm) (g y) := (hψ i).2 (g y) ⟨hgy, hi⟩
  have hFi : AnalyticAt ℂ (F ∘ (A.chart i).symm) ((A.chart i ∘ ψ.symm) (g y)) := by
    refine hF i _ ⟨(A.chart i).map_source hi, ?_⟩
    show (A.chart i).symm (A.chart i (ψ.symm (g y))) ∈ V
    rw [(A.chart i).left_inv hi]
    exact hV
  refine ((hFi.comp hτ).comp hg).congr ?_
  have hc : ContinuousAt (fun y' => ψ.symm (g y')) y := (ψ.continuousAt_symm hgy).comp hg.continuousAt
  filter_upwards [hc.preimage_mem_nhds ((A.chart i).open_source.mem_nhds hi)] with y' hy'
  simp only [Function.comp_apply, (A.chart i).left_inv hy']

theorem RefAlongSheet.proof : RefAlongSheet.Statement := by
  intro K _ ι _ P n M Xo A S γ y j hγ hsrc hev
  classical
  obtain ⟨g, hg'⟩ : ∃ g : (Fin n → ℂ) → Fin n → ℂ, g = fun y'' => S.R.chart j (M.proj (γ y'')) := ⟨_, rfl⟩
  have hg : AnalyticAt ℂ g y := by
    obtain ⟨V, hV, hVo, hyV⟩ := eventually_nhds_iff.1 (hev.mono fun _ h => h.2)
    refine AnalyticAt.pi fun i => ReciprocityTheory.AnForm.Osgood.osgood n V (fun w => g w i) hVo (fun z hz => ?_) y hyV
    rw [hg']
    exact (differentiableAt_pi.mp (hV z hz) i).differentiableWithinAt
  have hγc : ∀ p, AnalyticAt ℂ (fun w => γ w p) y := by
    intro p
    obtain ⟨V, hV, hVo, hyV⟩ := eventually_nhds_iff.1 (hγ.mono fun _ h => h.1)
    exact ReciprocityTheory.AnForm.Osgood.osgood n V (fun w => γ w p) hVo
      (fun z hz => (differentiableAt_pi.mp (hV z hz) p).differentiableWithinAt) y hyV
  have hgy : g y ∈ (S.R.chart j).target := by rw [hg']; exact (S.R.chart j).map_source hsrc
  have hxy : (S.R.chart j).symm (g y) = M.proj (γ y) := by rw [hg']; exact (S.R.chart j).left_inv hsrc
  obtain ⟨U, hUo, hx0U, hUth, s, hs, hsh, G1, hG1, hG1eq⟩ :=
    S.th_ref (M.proj (γ y)) (M.proj (γ y)) (S.R.th.mem_U _)
  obtain ⟨W, hWo, hx0W, G2, hG2, hG2eq⟩ := S.R.q_th j (M.proj (γ y)) (M.proj (γ y)) ⟨S.R.th.mem_U _, hsrc⟩
  obtain ⟨x', hx'⟩ : ∃ x' : (Fin n → ℂ) → M.Xc, x' = fun y' => (S.R.chart j).symm (g y') := ⟨_, rfl⟩
  have hsxy : x' y = M.proj (γ y) := by rw [hx']; exact hxy
  have hx'c : ContinuousAt x' y := by
    rw [hx']; exact ((S.R.chart j).continuousAt_symm hgy).comp hg.continuousAt
  have hsc : ∀ p, AnalyticAt ℂ (fun y' => s (x' y') p) y := fun p => by
    rw [hx']
    exact analyticAt_holoOn_comp_chartSymm (S.R.compat j) (hsh p) hg hgy (by rw [hxy]; exact hx0U)
  have hG1x : AnalyticAt ℂ (fun y' => G1 (x' y')) y := by
    rw [hx']
    exact analyticAt_holoOn_comp_chartSymm (S.R.compat j) hG1 hg hgy (by rw [hxy]; exact hx0U)
  have hG2x : AnalyticAt ℂ (fun y' => G2 (x' y')) y := by
    rw [hx']
    exact analyticAt_holoOn_comp_chartSymm (S.R.compat j) hG2 hg hgy (by rw [hxy]; exact hx0W)
  have hs0 : s (M.proj (γ y)) ∈ mcPts P := (hs _ hx0U).1
  choose i hi using hs0.1
  obtain ⟨cf, hcf⟩ : ∃ cf : K → (Fin n → ℂ) → ℂ,
      cf = fun k y' => γ y' ⟨k, i k⟩ / s (x' y') ⟨k, i k⟩ := ⟨_, rfl⟩
  have hsi : ∀ k, s (x' y) ⟨k, i k⟩ ≠ 0 := fun k => by rw [hsxy]; exact hi k
  have hcfa : ∀ k, AnalyticAt ℂ (cf k) y := fun k => by
    rw [hcf]; exact (hγc _).div (hsc _) (hsi k)
  have hne : ∀ᶠ y' in 𝓝 y, ∀ k, s (x' y') ⟨k, i k⟩ ≠ 0 :=
    Filter.eventually_all.2 fun k => (hsc _).continuousAt.eventually_ne (hsi k)
  have hUWn : U ∩ W ∈ 𝓝 (x' y) := (hUo.inter hWo).mem_nhds (by rw [hsxy]; exact ⟨hx0U, hx0W⟩)
  have hgood : ∀ᶠ y' in 𝓝 y, (x' y' ∈ U ∩ W ∧ M.proj (γ y') ∈ (S.R.chart j).source ∧ γ y' ∈ mcPts P) ∧
      ∀ k, s (x' y') ⟨k, i k⟩ ≠ 0 := by
    filter_upwards [hx'c.preimage_mem_nhds hUWn, hev, hγ, hne] with y' h1 h2 h3 h4
    exact ⟨⟨h1, h2.1, h3.2⟩, h4⟩
  have key : ∀ y', ((x' y' ∈ U ∩ W ∧ M.proj (γ y') ∈ (S.R.chart j).source ∧ γ y' ∈ mcPts P) ∧
      ∀ k, s (x' y') ⟨k, i k⟩ ≠ 0) →
      (∀ k, cf k y' ≠ 0) ∧ Real.log (S.ref.h (γ y')) = ∑ k, (S.ref.a k : ℝ) * Real.log ‖cf k y'‖ +
        (S.R.q j (S.R.chart j (M.proj (γ y'))) - (G2 (x' y')).re - (G1 (x' y')).re) := by
    rintro y' ⟨⟨⟨hU', hW'⟩, hsrc', hγ'⟩, hne'⟩
    have hxp : x' y' = M.proj (γ y') := by rw [hx', hg']; exact (S.R.chart j).left_inv hsrc'
    obtain ⟨hsm, hsp⟩ := hs _ hU'
    obtain ⟨c, hc, hγc'⟩ := (M.fibre _ hsm _ hγ').1 (by rw [hsp, hxp])
    have hck : ∀ k, cf k y' = c k := fun k => by
      have h := congrFun hγc' ⟨k, i k⟩
      rw [hcf]
      show γ y' ⟨k, i k⟩ / s (x' y') ⟨k, i k⟩ = c k
      rw [h]
      exact mul_div_cancel_right₀ (c k) (hne' k)
    have hh : S.ref.h (γ y') = (∏ k, ‖c k‖ ^ S.ref.a k) * S.ref.h (s (x' y')) := by
      rw [hγc']; exact S.ref.smul c _ hc
    have hpos : ∀ k, 0 < ‖c k‖ := fun k => norm_pos_iff.2 (hc k)
    have hlog : Real.log (S.ref.h (γ y')) =
        ∑ k, (S.ref.a k : ℝ) * Real.log ‖c k‖ + Real.log (S.ref.h (s (x' y'))) := by
      rw [hh, Real.log_mul (Finset.prod_pos fun k _ => zpow_pos (hpos k) _).ne' (S.ref.pos _ hsm.1).ne',
        Real.log_prod fun k _ => (zpow_pos (hpos k) _).ne']
      simp only [Real.log_zpow]
    have h1 := hG1eq _ hU'
    have hsrc'' : x' y' ∈ (S.R.chart j).source := by rw [hxp]; exact hsrc'
    have h2 := hG2eq _ ⟨⟨hW', hUth hU'⟩, hsrc''⟩
    refine ⟨fun k => by rw [hck]; exact hc k, ?_⟩
    rw [hlog, ← hxp]
    simp only [hck]
    linarith
  have hcy : ∀ k, cf k y ≠ 0 := (key y hgood.self_of_nhds).1
  refine ⟨fun y' => ∑ k, ((S.ref.a k : ℝ) : ℂ) * (Complex.log (cf k y' / cf k y) + (Real.log ‖cf k y‖ : ℂ)) -
    (G1 (x' y') + G2 (x' y')), ?_, ?_⟩
  · have hterm : ∀ k, AnalyticAt ℂ (fun y' => ((S.ref.a k : ℝ) : ℂ) *
        (Complex.log (cf k y' / cf k y) + (Real.log ‖cf k y‖ : ℂ))) y := fun k => by
      have hl : AnalyticAt ℂ (fun y' => Complex.log (cf k y' / cf k y)) y := by
        refine ((hcfa k).div analyticAt_const (hcy k)).clog ?_
        show cf k y / cf k y ∈ Complex.slitPlane
        rw [div_self (hcy k)]
        exact Complex.one_mem_slitPlane
      exact analyticAt_const.mul (hl.add analyticAt_const)
    have hsum : AnalyticAt ℂ (fun y' => ∑ k, ((S.ref.a k : ℝ) : ℂ) *
        (Complex.log (cf k y' / cf k y) + (Real.log ‖cf k y‖ : ℂ))) y := by
      have h := Finset.analyticAt_sum (𝕜 := ℂ) (f := fun k y' => ((S.ref.a k : ℝ) : ℂ) *
        (Complex.log (cf k y' / cf k y) + (Real.log ‖cf k y‖ : ℂ))) Finset.univ fun k _ => hterm k
      convert h using 1
      ext y'
      simp [Finset.sum_apply]
    have hG12 : AnalyticAt ℂ (fun y' => G1 (x' y') + G2 (x' y')) y := hG1x.add hG2x
    exact hsum.sub hG12
  · filter_upwards [hgood] with y' hy'
    obtain ⟨hnz, heq⟩ := key y' hy'
    rw [heq]
    have hl : ∀ k, Real.log ‖cf k y' / cf k y‖ = Real.log ‖cf k y'‖ - Real.log ‖cf k y‖ := fun k => by
      rw [norm_div, Real.log_div (norm_ne_zero_iff.2 (hnz k)) (norm_ne_zero_iff.2 (hcy k))]
    simp only [Complex.sub_re, Complex.add_re, Complex.re_sum, Complex.re_ofReal_mul, Complex.log_re,
      Complex.ofReal_re, hl, sub_add_cancel]
    ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def AmpleOnGenericFibre (P : Ideal (MRing ι)) (A : _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) : Prop :=
  ∀ (W : Ideal (MRing ι)) (d : ℕ), 1 ≤ d → IsArithVar W (d + 1) → P ≤ W → 0 < geomDeg W A d

def OffBoundary (Bd : Set ((Σ k, ι k) → ℂ)) (W : Ideal (MRing ι)) : Prop :=
  ∀ z ∈ mcPts W, z ∉ Bd

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

structure ComponentSetting (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] where

  H : HodgeData D

  Cd : CuspData D O Lt

  M : XModel D

  S : LogLogRegularisationSetting M D.Xo (muLine H)

  S_tied : S.IsTied

  S' : BoundedRegularisationSetting M D.Xo H.aMu (cuspCorr H Cd)

  S'_tied : S'.IsTied

  rd : ℝ

  Lval : ℝ

namespace ComponentSetting

variable {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]
  (X : ComponentSetting D O Lt)

abbrev MUq (B p q : ℕ) (t' : ℝ) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := MUc X.H X.S' B p q t'

def La (B : ℕ) : ℝ := abelian₂ B X.rd X.Lval

end ComponentSetting

variable {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

def CuspBundlePos (X : ComponentSetting D O Lt) : Prop :=
  ∀ B p q : ℕ, 4 * D.f + 2 ≤ B → 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    IsSemipositiveH (mCoordIdeal D.y) (X.MUq B p q t') ∧
      NefOnFibres (mCoordIdeal D.y) (X.MUq B p q t').a ∧
      AmpleOnGenericFibre (mCoordIdeal D.y) (X.MUq B p q t')

def HtInterior (Ch : ℝ) (X : ComponentSetting D O Lt) : Prop :=
  ∀ B p q : ℕ, 4 * D.f * D.N ^ 2 ≤ B → 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    ∀ W : Ideal (MRing ι), IsArithVar W 1 → mCoordIdeal D.y ≤ W → OffBoundary D.Bd W →
      -(Ch * D.f * D.j' * X.La B) - (p : ℝ) / q * D.KA ≤ htMUc X.H X.S' B p q t' W

def HtBoundary (Ch : ℝ) (X : ComponentSetting D O Lt) : Prop :=
  ∀ B p q : ℕ, 4 * D.f * D.N ^ 2 ≤ B → 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    ∀ W : Ideal (MRing ι), IsArithVar W 1 → mCoordIdeal D.y ≤ W → ¬ OffBoundary D.Bd W →
      -(Ch * D.f * D.j' * X.La B) - (p : ℝ) / q * D.KA ≤ htMUc X.H X.S' B p q t' W

def CuspMean (Cu : ℝ) (X : ComponentSetting D O Lt) : Prop :=
  1 ≤ D.j' → 3 * D.j' + 1 ≤ D.N → ∀ B : ℕ, 4 * D.f * D.N ^ 2 ≤ B →
    meanU X.H X.Cd ≤ Cu * D.f * D.j' * X.La B

def StokesLimit.Hyp (X : ComponentSetting D O Lt) (B : ℕ) (a : ℝ) : Prop :=
  ∀ p q : ℕ, 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    ((D.n + 1 : ℕ) : ℝ) * (a - (p : ℝ) / q * D.KA) * geomDegMUc X.H X.S' B p q t' ≤
      topMUc X.H X.S' B p q t'

def StokesLimit.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ) (a : ℝ),
    IsIntersectionSystem II → 4 * D.f + 2 ≤ B → ArLimExists X.H X.S B → StokesLimit.Hyp X B a →
      ((D.n + 1 : ℕ) : ℝ) * (a - meanU X.H X.Cd / 2) * degMu X.H ≤ arLim X.H X.S B

def GrassmannianHeightZTwo.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (cf : ℚ) (e : ℝ),
    IsIntersectionSystem II → 2 ≤ N → 1 ≤ j → j ≤ N - 1 → 0 < Jint Ψ N j cf →
    (∀ Z : Matrix (Fin (N - j)) (Fin j) ℂ, (∀ a b, ‖Z a b‖ = 1) →
      1 / 2 * Real.log (1 + Z * Z.conjTranspose).det.re ≤ e) →
    -hFl Ψ N II (FA Ψ N j cf) ≤
      ((dimN Ψ N j + 1 : ℕ) : ℝ) * (Jint Ψ N j cf : ℝ) * (Fintype.card Ψ : ℝ) * e

def MUConjInvariant (X : ComponentSetting D O Lt) : Prop :=
  ∀ B p q : ℕ, 4 * D.f + 2 ≤ B → 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    IsConjInvariantH (X.MUq B p q t')

def slX (X : ComponentSetting D O Lt) (B : ℕ) : ℝ :=
  arLim X.H X.S B / (((D.n + 1 : ℕ) : ℝ) * degMu X.H)

namespace Line

variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open Filter Topology Metric ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.AnForm (levi)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P : Ideal (MRing ι)} {d : ℕ} {M : CxModel P d} {Xo : Set ((Σ k, ι k) → ℂ)} {A : _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}

theorem LogLogRegularisationSetting.eventually_closedBall_subset (S : LogLogRegularisationSetting M Xo A) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, ∀ x ∈ closure (S.R.mid j),
      closedBall (S.R.chart j x) t ⊆ (S.R.chart j).target := by
  refine Filter.eventually_all.2 fun j => ?_
  have hc : IsCompact (closure (S.R.mid j)) := isClosed_closure.isCompact
  have himg : IsCompact (S.R.chart j '' closure (S.R.mid j)) :=
    hc.image_of_continuousOn ((S.R.chart j).continuousOn.mono (S.R.closure_mid j))
  have hsub : S.R.chart j '' closure (S.R.mid j) ⊆ (S.R.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (S.R.chart j).map_source (S.R.closure_mid j hx)
  obtain ⟨δ, hδ, hδs⟩ := himg.exists_cthickening_subset_open (S.R.chart j).open_target hsub
  filter_upwards [Ioo_mem_nhdsGT hδ] with t ht x hx
  exact (closedBall_subset_cthickening (Set.mem_image_of_mem _ hx) t).trans
    ((cthickening_mono ht.2.le _).trans hδs)

theorem LogLogRegularisationSetting.eventually_chartLevi (S : LogLogRegularisationSetting M Xo A) (hS : S.IsTied) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (S.regWeight t) ∧
      ∀ k : Fin S.R.N, ∀ x ∈ S.R.mid k, ∀ w : Fin d → ℂ,
        -(4 * S.Cη * S.e1 t) * ‖w‖ ^ 2 ≤
          levi (S.R.chartFun (S.regWeight t) k) (S.R.chart k x) w := by
  filter_upwards [self_mem_nhdsWithin, S.eventually_closedBall_subset, hS.compare] with t ht hball hcmp
  have hε : 0 < S.e1 t := lt_of_lt_of_le ht (S.e1_ge t ht)
  exact GroundTheory.Heights₂.Heights.Regular.GlueRegularised.full M.Xc d M.atlas S.R S.ρ S.η S.Cη (S.K t) t (S.e1 t)
    S.cutoff ht hε hball hcmp

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def HodgeFlagSpan.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (Pl : PlueckerData D) (H : HodgeData D)
    (B : AdaptedBasis H) (τ : Ψ) (i : Fin (D.N - 1)),
    Submodule.span Ω (Set.range (Pl.pluecker0 B τ i)) =
      Submodule.span Ω (Set.range (flagMinor (genMat0Fr Ω Ψ D.N D.j τ) i))

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
