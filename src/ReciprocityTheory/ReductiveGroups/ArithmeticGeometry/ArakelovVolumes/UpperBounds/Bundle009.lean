module

public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import ReciprocityTheory.L2DbarEstimates.SkodaWeights.Bundle001
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle008
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle006
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE

open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD

variable {f p q N' : ℕ}

theorem two_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := by
  first
  | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
  | exact WithTop.coe_le_coe.mpr le_top
  | simp

theorem sqNorm_nonneg' {m : ℕ} (g : Fin m → ℂ) : 0 ≤ sqNorm g :=
  Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhF

open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE

variable {f p q N' : ℕ}

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhF
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace UpDivC

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric Set Filter

variable {n : ℕ}

theorem dense_nonzero {U : Set (V n)} (hU : IsOpen U) (hUc : IsPreconnected U) {g : V n → ℂ}
    (hg : DifferentiableOn ℂ g U) (hg0 : ∃ z ∈ U, g z ≠ 0) {z : V n} (hz : z ∈ U) :
    ∃ᶠ y in 𝓝 z, y ∈ U ∧ g y ≠ 0 := by
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  have hz0 : ∀ᶠ y in 𝓝 z, g y = 0 := by
    filter_upwards [hcon, hU.mem_nhds hz] with y hy hyU
    by_contra h
    exact hy ⟨hyU, h⟩
  have hsub : U ⊆ {y | ∀ᶠ x in 𝓝 y, g x = 0} := by
    refine hUc.subset_of_closure_inter_subset isOpen_setOf_eventually_nhds ⟨z, hz, hz0⟩ ?_
    rintro y ⟨hycl, hyU⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU y hyU
    obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.mp hycl ε hε
    have hbb : b ∈ ball y ε := by
      rw [mem_ball, dist_comm]
      exact hdist
    have hEq := ReciprocityTheory.L2DbarEstimates.C.ident n (ball y ε) g b isOpen_ball (convex_ball y ε)
      (hg.mono hball) hbb hb
    exact Filter.eventually_of_mem (ball_mem_nhds y hε) (fun w hw => by simpa using hEq hw)
  obtain ⟨w, hwU, hw⟩ := hg0
  exact hw (hsub hwU).self_of_nhds

theorem ext_glue {U : Set (V n)} (hU : IsOpen U) (hUc : IsPreconnected U) {g : V n → ℂ}
    (hg : DifferentiableOn ℂ g U) (hg0 : ∃ z ∈ U, g z ≠ 0) {H : V n → ℂ}
    (hH : DifferentiableOn ℂ H (U ∩ {z | g z ≠ 0}))
    (hloc : ∀ z ∈ U, ∃ r > 0, ball z r ⊆ U ∧
      IntegrableOn (fun y => ‖H y‖ ^ 2) (ball z r \ {y | g y = 0})) :
    ∃ H' : V n → ℂ, DifferentiableOn ℂ H' U ∧ EqOn H' H (U ∩ {z | g z ≠ 0}) := by
  classical
  choose! r hr hrU hint using hloc

  have hE : ∀ z ∈ U, ∃ E : V n → ℂ, DifferentiableOn ℂ E (ball z (r z)) ∧
      EqOn E H (ball z (r z) \ {y | g y = 0}) := by
    intro z hz
    exact ReciprocityTheory.L2DbarEstimates.C.ext n (ball z (r z)) g H isOpen_ball (hg.mono (hrU z hz))
      (hH.mono (fun y hy => ⟨hrU z hz hy.1, hy.2⟩)) (hint z hz)
  choose! E hEd hEe using hE

  have hagree : ∀ y ∈ U, ∀ z ∈ U, ∀ w ∈ ball y (r y) ∩ ball z (r z), E y w = E z w := by
    intro y hy z hz w hw
    have hwU : w ∈ U := hrU y hy hw.1
    have hopen : IsOpen (ball y (r y) ∩ ball z (r z)) := isOpen_ball.inter isOpen_ball
    have hc1 : ContinuousAt (E y) w :=
      (hEd y hy).continuousOn.continuousAt (isOpen_ball.mem_nhds hw.1)
    have hc2 : ContinuousAt (E z) w :=
      (hEd z hz).continuousOn.continuousAt (isOpen_ball.mem_nhds hw.2)
    have hfreq : ∃ᶠ v in 𝓝 w, E y v - E z v ∈ ({0} : Set ℂ) := by
      have h1 := (dense_nonzero hU hUc hg hg0 hwU).and_eventually
        (hopen.mem_nhds hw : ∀ᶠ v in 𝓝 w, v ∈ ball y (r y) ∩ ball z (r z))
      refine h1.mono ?_
      rintro v ⟨⟨-, hgv⟩, hv1, hv2⟩
      rw [Set.mem_singleton_iff, sub_eq_zero, hEe y hy ⟨hv1, hgv⟩, hEe z hz ⟨hv2, hgv⟩]
    have h0 := isClosed_singleton.mem_of_frequently_of_tendsto hfreq (hc1.sub hc2)
    simpa [sub_eq_zero] using h0
  refine ⟨fun w => E w w, ?_, ?_⟩
  · intro z hz
    have hev : (fun w => E w w) =ᶠ[𝓝 z] E z := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (hr z hz)), hU.mem_nhds hz]
        with w hw hwU
      exact hagree w hwU z hz w ⟨mem_ball_self (hr w hwU), hw⟩
    exact (((hEd z hz).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self (hr z hz)))).congr_of_eventuallyEq hev).differentiableWithinAt
  · rintro w ⟨hwU, hgw⟩
    exact hEe w hwU ⟨mem_ball_self (hr w hwU), hgw⟩

end UpDivC

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

private lemma gram_eq_lemma (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [FD.gram, FD.hermC, FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

private lemma gram_mul_lemma_2 (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P Q : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (P * Q) = Qᵀ * gram τ G P * Q.map (starRingEnd ℂ) := by
  rw [gram_eq_lemma, gram_eq_lemma, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

theorem dom_rmul {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) : rmul x b ∈ X.dom := by
  rw [X.mem_dom_iff] at hx ⊢
  intro τ
  have hN := FrameDegreeData.upper_of_bor (X := X) hb τ
  have hbd := (hb τ).1
  refine ⟨?_, fun i => ?_⟩
  · show (mat x τ * mat b τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (hx τ).1 hbd
  · have hd := (hx τ).2 i
    have hdiag : ∀ j, mat b τ j j ≠ 0 := by
      intro j
      rw [Matrix.det_of_upperTriangular hN] at hbd
      exact Finset.prod_ne_zero_iff.1 hbd j (Finset.mem_univ j)
    have hP0 : (∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
        (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j _ => hdiag _
    have heq : dmin X.Gm (rmul x b) τ i = dmin X.Gm x τ i *
        (Complex.normSq (∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
          (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) : ℂ) := by
      show lminor (gram τ.1 X.Gm (mat x τ * mat b τ)) i = _
      rw [gram_mul_lemma_2, FrameDegreeData.lminor_conj hN,
        show ∀ z w : ℂ, z * w * conj z = w * (z * conj z) from fun z w => by ring, Complex.mul_conj]
      rfl
    rw [heq, Complex.re_mul_ofReal, ← mul_assoc]
    exact mul_pos hd (Complex.normSq_pos.2 hP0)

theorem stab_mat {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    (γ : Matrix (Fin r) (Fin r) E)ᵀ * X.Gm * (γ : Matrix (Fin r) (Fin r) E).map cc = X.Gm := by
  have hst := (X.Γ_stab γ hγ).1
  ext i j
  have h := hst (Pi.single i 1) (Pi.single j 1)
  have hR : herm X.Gm (Pi.single i (1 : E)) (Pi.single j 1) = X.Gm i j := by
    simp [herm, Pi.single_apply, cc, apply_ite]
  have hL : herm X.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single i 1)
      ((γ : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single j 1) =
      ((γ : Matrix (Fin r) (Fin r) E)ᵀ * X.Gm * (γ : Matrix (Fin r) (Fin r) E).map cc) i j := by
    simp only [herm, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [← hL, h, hR]

theorem gram_gam {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (τ : X.Ψ) :
    gram τ.1 X.Gm ((γ : Matrix (Fin r) (Fin r) E).map τ.1) = X.Gm.map τ.1 := by
  have h := stab_mat X hγ
  rw [gram_eq_lemma]
  conv_rhs => rw [← h]
  ext a b

  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, emb_cc]

theorem gram_lact {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (lact γ x) τ) = gram τ.1 X.Gm (mat x τ) := by
  show gram τ.1 X.Gm ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) = _
  rw [gram_mul_lemma_2, gram_gam X hγ τ, gram_eq_lemma]

theorem dom_lact {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact γ x ∈ X.dom := by
  rw [X.mem_dom_iff] at hx ⊢
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · show ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ).det ≠ 0
    rw [Matrix.det_mul]
    refine mul_ne_zero ?_ (hx τ).1
    have h1 : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det = τ.1 (γ : Matrix (Fin r) (Fin r) E).det := by
      rw [RingHom.map_det]
      rfl
    rw [h1]
    exact (map_ne_zero τ.1).2 (Matrix.isUnits_det_units γ).ne_zero
  · have := (hx τ).2 i
    simpa only [dmin, gram_lact X hγ x τ] using this

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS
end
