module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfI
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.L2DbarEstimates.NormFibrations.MvBlowup
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoD

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Set Metric

noncomputable section

variable {n : ℕ} {Ω : Set (V n)} {g : V n → ℂ}

theorem not_loc_zero (hΩ : IsOpen Ω) (hc : IsPreconnected Ω) (hg : DifferentiableOn ℂ g Ω)
    (hne : ∃ z ∈ Ω, g z ≠ 0) : ∀ z ∈ Ω, ¬ g =ᶠ[𝓝 z] 0 := by
  intro z hz hzero
  obtain ⟨z0, hz0, hgz0⟩ := hne
  set u := {w : V n | ∀ᶠ y in 𝓝 w, g y = (0 : V n → ℂ) y} with hu_def
  set v := {w : V n | ∀ᶠ y in 𝓝 w, ¬ (g =ᶠ[𝓝 y] 0)} with hv_def
  have hu : IsOpen u := isOpen_setOfPred_eventually_nhds
  have hv : IsOpen v := isOpen_setOfPred_eventually_nhds
  have hcov : Ω ⊆ u ∪ v := by
    intro w hw
    by_contra hcon
    simp only [mem_union, not_or] at hcon
    obtain ⟨hnu, hnv⟩ := hcon
    obtain ⟨ρ, hρ, hB⟩ := Metric.isOpen_iff.1 hΩ w hw
    have hfr : ∃ᶠ y in 𝓝 w, g =ᶠ[𝓝 y] 0 := by
      rw [Filter.Frequently]; intro h; exact hnv h
    obtain ⟨y, hy1, hy2⟩ := (hfr.and_eventually (ball_mem_nhds w hρ)).exists
    have hB0 := C.ident n (ball w ρ) g y isOpen_ball (convex_ball w ρ) (hg.mono hB) hy2 hy1
    exact hnu (Filter.eventually_of_mem (ball_mem_nhds w hρ) fun x hx => hB0 hx)
  have hv0 : z0 ∈ v := by
    have hct : ContinuousAt g z0 := hg.continuousOn.continuousAt (hΩ.mem_nhds hz0)
    have hev : ∀ᶠ y in 𝓝 z0, g y ≠ 0 := hct.eventually_ne hgz0
    exact hev.mono fun y hy h => hy (by simpa using h.eq_of_nhds)
  obtain ⟨w, -, hwu, hwv⟩ := hc u v hu hv hcov ⟨z, hz, hzero⟩ ⟨z0, hz0, hv0⟩
  obtain ⟨y, hy1, hy2⟩ := ((Filter.Eventually.eventually_nhds hwu).and hwv).exists
  exact hy2 hy1

theorem null_zero (hΩ : IsOpen Ω) (hc : IsPreconnected Ω) (hg : DifferentiableOn ℂ g Ω)
    (hne : ∃ z ∈ Ω, g z ≠ 0) : volume (Ω ∩ {z | g z = 0}) = 0 := by
  apply measure_null_of_locally_null
  intro x hx
  obtain ⟨ρ, hρ, hB⟩ := Metric.isOpen_iff.1 hΩ x hx.1
  refine ⟨(Ω ∩ {z | g z = 0}) ∩ ball x ρ, inter_mem_nhdsWithin _ (ball_mem_nhds x hρ), ?_⟩
  have hnz : ∃ y ∈ ball x ρ, g y ≠ 0 := by
    by_contra h
    push Not at h
    exact not_loc_zero hΩ hc hg hne x hx.1
      (Filter.eventually_of_mem (ball_mem_nhds x hρ) fun y hy => h y hy)
  exact measure_mono_null (fun y hy => by
    simp only [mem_inter_iff, mem_setOf_eq, Metric.mem_ball] at hy ⊢; tauto) (extNull n x ρ g (hg.mono hB) hnz)

theorem ext_glue (hΩ : IsOpen Ω) (hc : IsPreconnected Ω) (hg : DifferentiableOn ℂ g Ω)
    (hne : ∃ z ∈ Ω, g z ≠ 0) {F' : V n → ℂ} (hF' : DifferentiableOn ℂ F' {z | z ∈ Ω ∧ g z ≠ 0})
    (hL2 : ∀ z ∈ Ω, ∃ ρ > 0, ball z ρ ⊆ Ω ∧
      ∫⁻ y in ball z ρ \ {y | g y = 0}, ENNReal.ofReal (‖F' y‖ ^ 2) < ⊤) :
    ∃ F : V n → ℂ, DifferentiableOn ℂ F Ω ∧ ∀ z ∈ Ω, g z ≠ 0 → F z = F' z := by
  classical
  have hU : ∀ z ∈ Ω, ∃ ρ > 0, ball z ρ ⊆ Ω ∧ ∃ U : V n → ℂ, DifferentiableOn ℂ U (ball z ρ) ∧
      EqOn U F' (ball z ρ \ {y | g y = 0}) := by
    intro z hz
    obtain ⟨ρ, hρ, hB, hI⟩ := hL2 z hz
    obtain ⟨U, hU1, hU2⟩ := ext n z ρ g F' (hg.mono hB) (hF'.mono fun y hy => ⟨hB hy.1, hy.2⟩) hI
    exact ⟨ρ, hρ, hB, U, hU1, hU2⟩
  choose! ρ hρ hB U hUd hEq using hU
  let F : V n → ℂ := fun z => if g z ≠ 0 then F' z else U z z
  have key : ∀ z0 ∈ Ω, ∀ w ∈ ball z0 (ρ z0), F w = U z0 w := by
    intro z0 hz0 w hw
    by_cases hgw : g w = 0
    · have hwΩ : w ∈ Ω := hB z0 hz0 hw
      simp only [F, hgw, ne_eq, not_true_eq_false, if_false]
      by_contra hne'
      have hN : ∀ᶠ y in 𝓝 w, y ∈ ball z0 (ρ z0) ∩ ball w (ρ w) :=
        (isOpen_ball.inter isOpen_ball).mem_nhds ⟨hw, mem_ball_self (hρ w hwΩ)⟩
      have h1 : ContinuousAt (U z0) w :=
        ((hUd z0 hz0).differentiableAt (isOpen_ball.mem_nhds hw)).continuousAt
      have h2 : ContinuousAt (U w) w :=
        ((hUd w hwΩ).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (hρ w hwΩ)))).continuousAt
      have hev : ∀ᶠ y in 𝓝 w, U w y - U z0 y ≠ 0 := (h2.sub h1).eventually_ne (sub_ne_zero.2 hne')
      have hfr : ∃ᶠ y in 𝓝 w, g y ≠ 0 := by
        rw [Filter.Frequently]
        intro h
        exact not_loc_zero hΩ hc hg hne w hwΩ (h.mono fun y hy => by simpa using hy)
      obtain ⟨y, hy1, hy2, hy3⟩ := (hfr.and_eventually (hN.and hev)).exists
      exact hy3 (sub_eq_zero.2 ((hEq w hwΩ ⟨hy2.2, hy1⟩).trans (hEq z0 hz0 ⟨hy2.1, hy1⟩).symm))
    · simp only [F, ne_eq, hgw, not_false_eq_true, if_true]
      exact (hEq z0 hz0 ⟨hw, hgw⟩).symm
  refine ⟨F, fun z0 hz0 => ?_, fun z _ hgz => by simp [F, hgz]⟩
  have hd : DifferentiableAt ℂ (U z0) z0 :=
    (hUd z0 hz0).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (hρ z0 hz0)))
  refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
  exact Filter.eventually_of_mem (ball_mem_nhds z0 (hρ z0 hz0)) fun w hw => key z0 hz0 w hw

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoD
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.HE

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ENNReal

noncomputable section

variable {n : ℕ} {U : Set (V n)}

theorem ext_glue (hU : IsOpen U) (g G : V n → ℂ) (hg : DifferentiableOn ℂ g U)
    (hgn : ∀ W : Set (V n), IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, g y ≠ 0)
    (hG : DifferentiableOn ℂ G {y | y ∈ U ∧ g y ≠ 0})
    (hL : ∀ p ∈ U, ∃ ρ > 0, ball p ρ ⊆ U ∧
      ∫⁻ y in ball p ρ \ {y | g y = 0}, ENNReal.ofReal (‖G y‖ ^ 2) < ⊤) :
    ∃ G' : V n → ℂ, DifferentiableOn ℂ G' U ∧ Set.EqOn G' G {y | y ∈ U ∧ g y ≠ 0} := by
  classical
  have hloc : ∀ p ∈ U, ∃ ρ > 0, ball p ρ ⊆ U ∧ ∃ F : V n → ℂ, DifferentiableOn ℂ F (ball p ρ) ∧
      Set.EqOn F G (ball p ρ \ {y | g y = 0}) := by
    intro p hp
    obtain ⟨ρ, hρ, hsub, hint⟩ := hL p hp
    obtain ⟨F, hF, hFeq⟩ := ReciprocityTheory.L2DbarEstimates.ext n p ρ g G (hg.mono hsub)
      (hG.mono fun y hy => ⟨hsub hy.1, hy.2⟩) hint
    exact ⟨ρ, hρ, hsub, F, hF, hFeq⟩
  choose ρ hρ hsub F hF hFeq using hloc
  have agree : ∀ y (hy : y ∈ U) z (hz : z ∈ U) x, x ∈ ball y (ρ y hy) → x ∈ ball z (ρ z hz) →
      F y hy x = F z hz x := by
    intro y hy z hz x hxy hxz
    by_contra hne
    have hcy : ContinuousAt (F y hy) x :=
      (hF y hy).continuousOn.continuousAt (isOpen_ball.mem_nhds hxy)
    have hcz : ContinuousAt (F z hz) x :=
      (hF z hz).continuousOn.continuousAt (isOpen_ball.mem_nhds hxz)
    have hev : ∀ᶠ t in 𝓝 x, F y hy t ≠ F z hz t := by
      first
        | exact hcy.eventually_ne hcz hne
        | exact ((hcy.sub hcz).eventually_ne (sub_ne_zero.mpr hne)).mono fun t ht h => ht (sub_eq_zero.mpr h)
    have hs : {t | t ∈ ball y (ρ y hy) ∧ t ∈ ball z (ρ z hz) ∧ F y hy t ≠ F z hz t} ∈ 𝓝 x :=
      Filter.inter_mem (isOpen_ball.mem_nhds hxy) (Filter.inter_mem (isOpen_ball.mem_nhds hxz) hev)
    obtain ⟨W, hWs, hWo, hxW⟩ := _root_.mem_nhds_iff.mp hs
    obtain ⟨t, htW, hgt⟩ := hgn W hWo (fun t ht => hsub y hy (hWs ht).1) ⟨x, hxW⟩
    have h1 := hFeq y hy ⟨(hWs htW).1, hgt⟩
    have h2 := hFeq z hz ⟨(hWs htW).2.1, hgt⟩
    exact (hWs htW).2.2 (h1.trans h2.symm)
  refine ⟨fun y => if hy : y ∈ U then F y hy y else 0, ?_, ?_⟩
  · intro y hy
    have hnb : ball y (ρ y hy) ∈ 𝓝 y := isOpen_ball.mem_nhds (mem_ball_self (hρ y hy))
    have heq : (fun y => if hy : y ∈ U then F y hy y else 0) =ᶠ[𝓝 y] F y hy := by
      filter_upwards [hnb] with x hx
      have hxU : x ∈ U := hsub y hy hx
      rw [dite_eq_left hxU]
      exact agree x hxU y hy x (mem_ball_self (hρ x hxU)) hx
    exact (((hF y hy).differentiableAt hnb).congr_of_eventuallyEq heq).differentiableWithinAt
  · intro y hy
    show (if h : y ∈ U then F y h y else 0) = G y
    rw [dite_eq_left hy.1]
    exact hFeq y hy.1 ⟨mem_ball_self (hρ y hy.1), hy.2⟩

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.HE
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
  Asymptotics ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem nmat_zero' (τ : X.Ψ) : mat (nmat X (0 : V (nd X))) τ = 1 := by
  ext a b
  by_cases h : b < a
  · have hab : a ≠ b := by rintro rfl; exact lt_irrefl _ h
    simp [mat, nmat, h, hab, Matrix.one_apply]
    rfl
  · by_cases hab : a = b
    · subst hab; simp [mat, nmat]
    · simp [mat, nmat, h, hab, Matrix.one_apply]

theorem cpt_zero' (x0 : Frame X.Ψ r) : cpt X x0 0 = x0 := by
  funext τ
  show mat x0 τ * mat (nmat X (0 : V (nd X))) τ = x0 τ
  rw [nmat_zero', mul_one]
  rfl

theorem nmat_zero_mem : nmat X (0 : V (nd X)) ∈ Bor X.Ψ r := by
  simp only [Bor, Set.mem_setOf_eq]
  intro τ
  refine ⟨?_, fun a c hca => ?_⟩
  · rw [nmat_zero']; simp
  · simp [nmat, hca]
    rfl

theorem lact_one' (y : Frame X.Ψ r) : lact (1 : GL (Fin r) E) y = y := by
  funext τ
  simp only [lact, Units.val_one]
  rw [Matrix.map_one _ (map_zero _) (map_one _), one_mul]
  rfl

theorem s_xs_zero {Xa : ArchInM X} (Fl : FlatM X Xa) (j : Fin Fl.δ) (k : Fin (nd X)) :
    Fl.s k (Fl.xs j) = 0 := by
  have he : Fl.xs j = lact (1 : GL (Fin r) E) (rmul (Fl.xs j) (nmat X 0)) := by
    rw [lact_one']
    exact (cpt_zero' X (Fl.xs j)).symm
  exact (Fl.S_eq (Fl.xs j) (Fl.xs_mem j)).mpr ⟨j, 1, X.Γ.one_mem, nmat X 0, nmat_zero_mem X, he⟩ k

theorem anal_loc {P : Frame X.Ψ r → ℂ} (hP : DifferentiableOn ℂ P X.dom) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) : AnalyticAt ℂ (fun z => P (cpt X x z)) 0 := by
  have hc := OntoB.cd_cpt X x
  have hU : IsOpen {z : V (nd X) | cpt X x z ∈ X.dom} :=
    (FourierCoefficientDomain.isOpen_dom X).preimage hc.continuous
  refine DivLA.analyticAt_of_diffOn hU ?_ (by simpa [cpt_zero'] using hx)
  exact hP.comp (hc.differentiable (by simp)).differentiableOn (fun z hz => hz)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf Topology

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem bigCell_of (hLU : LUStatement (E := E)) : BigCellStatement (E := E) := by
  intro r X x0 hx0 la P hP hvan x hx
  obtain ⟨Δ, zOf, bOf, -, hdense, -, -, hdec, -⟩ := hLU r X x0 hx0

  have hgood : ∀ y ∈ X.dom, Δ y ≠ 0 → P y = 0 := by
    intro y hy hΔ
    obtain ⟨hz, hb, hyeq⟩ := hdec y hy hΔ
    have h1 : P (rmul (cpt X x0 (zOf y)) (bOf y)) = bchar la (bOf y) * P (cpt X x0 (zOf y)) :=
      hP.2 (cpt X x0 (zOf y)) hz (bOf y) hb
    have h2 : P (cpt X x0 (zOf y)) = 0 := hvan (zOf y) hz
    rw [hyeq, h1, h2, mul_zero]

  have hopen : IsOpen X.dom := by
    have hmat : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => mat x τ := by
      intro τ
      first
      | exact continuous_apply τ
      | (unfold mat; exact continuous_apply τ)
      | fun_prop
      | continuity
    have hgram : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => gram τ.1 X.Gm (mat x τ) := by
      intro τ
      refine continuous_matrix fun a b => ?_
      simp only [gram, hermC, col, Matrix.of_apply]
      have h := hmat τ
      first
      | fun_prop
      | continuity
    have hdet : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => (mat x τ).det :=
      fun τ => (hmat τ).matrix_det
    have hmin : ∀ τ : X.Ψ, ∀ i : Fin (r + 1), Continuous fun x : Frame X.Ψ r => (dmin X.Gm x τ i).re := by
      intro τ i
      unfold dmin lminor
      exact Complex.continuous_re.comp ((hgram τ).matrix_submatrix _ _).matrix_det
    show IsOpen (GG X.Ψ X.Gm X.p0)
    have hset : GG X.Ψ X.Gm X.p0 = ⋂ τ : X.Ψ, ({x | (mat x τ).det ≠ 0} ∩
        ⋂ i : Fin (r + 1), {x | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
      ext x
      simp only [GG, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
    rw [hset]
    exact isOpen_iInter_of_finite fun τ => (isOpen_ne_fun (hdet τ) continuous_const).inter
      (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_const.mul (hmin τ i)))
  have hcont : ContinuousOn P X.dom := hP.1.continuousOn
  by_contra hne
  have hU : IsOpen (X.dom ∩ P ⁻¹' {0}ᶜ) := hcont.isOpen_inter_preimage hopen isOpen_compl_singleton
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x ⟨hx, hne⟩
  obtain ⟨y, hy, hΔ⟩ := hdense x hx ε hε
  have hy' := hball hy
  have h0 := hgood y hy'.1 hΔ
  exact hy'.2 h0

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData Finset

noncomputable section

attribute [local instance] Classical.propDecidable

lemma prod_min_range (f : ℕ → ℝ) (n : ℕ) :
    ∏ a ∈ range n, ∏ b ∈ range n, f (min a b) = (∏ i ∈ range n, (∏ k ∈ range i, f k) ^ 2) * ∏ k ∈ range n, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ∀ a ∈ range n, ∏ b ∈ range (n + 1), f (min a b) = (∏ b ∈ range n, f (min a b)) * f a := by
      intro a ha
      rw [prod_range_succ, min_eq_left (le_of_lt (mem_range.mp ha))]
    have h2 : ∏ b ∈ range (n + 1), f (min n b) = (∏ b ∈ range n, f b) * f n := by
      rw [prod_range_succ, min_self]
      congr 1
      exact prod_congr rfl fun b hb => by rw [min_eq_right (le_of_lt (mem_range.mp hb))]
    rw [prod_range_succ (fun a => ∏ b ∈ range (n + 1), f (min a b)) n, prod_congr rfl h1, prod_mul_distrib, ih, h2,
      prod_range_succ (fun i => (∏ k ∈ range i, f k) ^ 2) n, prod_range_succ f n]
    ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma upper_mul_diag {A B : Matrix (Fin r) (Fin r) ℂ} (hA : A.BlockTriangular id) (hB : B.BlockTriangular id)
    (k : Fin r) : (A * B) k k = A k k * B k k := by
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · intro j _ hjk
    rcases lt_or_gt_of_ne hjk with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

lemma bOf_diag (y : Frame X.Ψ r) (τ : X.Ψ) (k : Fin r) : mat (bOf X y) τ k k = sOf X y τ k := by
  have h1 : mat (bOf X y) τ k k = uOf X y τ k k * sOf X y τ k := by
    show (uOf X y τ * Matrix.diagonal (sOf X y τ)) k k = _
    rw [Matrix.mul_diagonal]
  rw [h1]
  have h2 : uOf X y τ k k = 1 := by
    show uMat _ k k = 1
    unfold uMat
    simp
  rw [h2, one_mul]

lemma normSq_β0_diag {y : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) (k : Fin r) :
    Complex.normSq (β0 X y τ k k) = |(dOf X y τ k).re| := by
  have hinv : β0 X y τ * mat (bOf X y) τ = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (bOf_det X hy τ))
  have h1 := congrFun (congrFun hinv k) k
  rw [upper_mul_diag (β0_upper X hy τ) (upper_of_bor X (bOf_mem X hy) τ), bOf_diag, Matrix.one_apply_eq] at h1
  have hpos := abs_re_pos X hy τ k
  have hs : Complex.normSq (sOf X y τ k) = |(dOf X y τ k).re|⁻¹ := by
    rw [sOf, Complex.normSq_ofReal, ← pow_two, inv_pow, Real.sq_sqrt (abs_nonneg _)]
  have h2 := congrArg Complex.normSq h1
  rw [Complex.normSq_mul, hs, map_one] at h2
  field_simp at h2
  linarith

def δ (y : Frame X.Ψ r) (τ : X.Ψ) (k : Fin r) : ℝ := |(dOf X y τ k).re|

def fδ (y : Frame X.Ψ r) (τ : X.Ψ) (k : ℕ) : ℝ := if h : k < r then δ X y τ ⟨k, h⟩ else 1

lemma normSq_det_jac {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    Complex.normSq (LinearMap.det (Lβ (β0 X y))) * Complex.normSq (jacβ (β0 X y)) =
      ∏ i : Ix X.Ψ r, δ X y i.1 (min i.2.1 i.2.2) := by
  rw [det_Lβ _ (β0_upper X hy), jacβ, map_prod, map_prod]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i : Ix X.Ψ r => i.2.2 < i.2.1)
    (fun i => δ X y i.1 (min i.2.1 i.2.2))]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i : Ix X.Ψ r => i.2.2 < i.2.1)
    (fun i => Complex.normSq (if i.2.2 < i.2.1 then β0 X y i.1 i.2.2 i.2.2 else 1))]
  have e1 : ∏ i : UpI X.Ψ r, Complex.normSq (β0 X y i.1.1 i.1.2.1 i.1.2.1) =
      ∏ i : {i : Ix X.Ψ r // ¬ i.2.2 < i.2.1}, δ X y i.1.1 (min i.1.2.1 i.1.2.2) :=
    Finset.prod_congr rfl fun i _ => by rw [normSq_β0_diag X hy, min_eq_left (not_lt.1 i.2)]; rfl
  have e2 : ∏ i : {i : Ix X.Ψ r // ¬ i.2.2 < i.2.1},
      Complex.normSq (if i.1.2.2 < i.1.2.1 then β0 X y i.1.1 i.1.2.2 i.1.2.2 else 1) = 1 :=
    Finset.prod_eq_one fun i _ => by rw [if_neg i.2, map_one]
  have e3 : ∏ i : {i : Ix X.Ψ r // i.2.2 < i.2.1},
      Complex.normSq (if i.1.2.2 < i.1.2.1 then β0 X y i.1.1 i.1.2.2 i.1.2.2 else 1) =
      ∏ i : {i : Ix X.Ψ r // i.2.2 < i.2.1}, δ X y i.1.1 (min i.1.2.1 i.1.2.2) :=
    Finset.prod_congr rfl fun i _ => by rw [if_pos i.2, normSq_β0_diag X hy, min_eq_right i.2.le]; rfl
  rw [e1, e2, e3, mul_one, mul_comm]

lemma norm_dmin {y : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖dmin X.Gm y τ i‖ = ∏ k ∈ range i, fδ X y τ k := by
  rw [dmin_prod X hy τ i, norm_prod, ← Fin.prod_univ_eq_prod_range (fδ X y τ)]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hj : (j : ℕ) < r := lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ i.isLt)
  rw [fδ, dite_eq_left hj, δ]
  have hre := dOf_real X hy τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
  have hc : Fin.castLE (Nat.le_of_lt_succ i.isLt) j = (⟨j, hj⟩ : Fin r) := Fin.ext rfl
  rw [hc] at hre ⊢
  exact (Complex.abs_re_eq_norm.2 hre).symm

theorem exponent_identity {y : Frame X.Ψ r} (hy : y ∈ X.dom) (hlast : ∀ τ, ‖dmin X.Gm y τ (Fin.last r)‖ = 1) :
    Complex.normSq (LinearMap.det (Lβ (β0 X y))) * Complex.normSq (jacβ (β0 X y)) =
      ∏ τ, ∏ i : Fin r, ‖dmin X.Gm y τ i.castSucc‖ ^ 2 := by
  have hτ : ∀ τ : X.Ψ, ∏ a : Fin r, ∏ b : Fin r, δ X y τ (min a b) =
      ∏ i : Fin r, ‖dmin X.Gm y τ i.castSucc‖ ^ 2 := by
    intro τ
    have hp := prod_min_range (fδ X y τ) r
    have hl : ∏ k ∈ range r, fδ X y τ k = 1 := by
      have h1 := norm_dmin X hy τ (Fin.last r)
      rw [hlast τ, Fin.val_last] at h1
      exact h1.symm
    rw [hl, mul_one] at hp
    have hd : ∀ i : Fin r, ‖dmin X.Gm y τ i.castSucc‖ = ∏ k ∈ range (i : ℕ), fδ X y τ k := by
      intro i
      rw [norm_dmin X hy τ i.castSucc, Fin.coe_castSucc]
    have e1 : ∀ a b : Fin r, δ X y τ (min a b) = fδ X y τ (min (a : ℕ) (b : ℕ)) := by
      intro a b
      unfold fδ
      rw [dite_eq_left (min_lt_of_left_lt a.isLt)]
      congr 1
    simp only [hd, e1]
    simp only [Finset.prod_range] at hp ⊢
    exact hp
  rw [normSq_det_jac X hy]
  unfold Ix
  simp only [Fintype.prod_prod_type]
  exact Finset.prod_congr rfl fun τ _ => hτ τ

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end
