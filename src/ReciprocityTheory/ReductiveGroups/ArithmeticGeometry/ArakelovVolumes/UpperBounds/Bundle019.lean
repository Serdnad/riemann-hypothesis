module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle017
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.CurvatureStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantNormalForms
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfI
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle013

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf ReciprocityTheory.L2DbarEstimates Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def coefR {r : ℕ} (X : Data E r) (v : X.Ψ → Fin r → ℝ) (τ : X.Ψ) (a j : Fin r) : ℝ :=
  Dsg X j / Dsg X a * (v τ a - v τ j)

theorem coefR_nonneg {r : ℕ} (X : Data E r) (v : X.Ψ → Fin r → ℝ) (hv : IsDominantR X v) (τ : X.Ψ)
    (a j : Fin r) (h : (a : ℕ) < j) : 0 ≤ coefR X v τ a j := by
  obtain ⟨h1, h2, h3⟩ := hv τ
  have hle : a ≤ j := Fin.le_iff_val_le_val.mpr h.le
  have f1 := fun (hj : (j : ℕ) < X.p0) => h1 a j hle hj
  have f2 := fun (ha : X.p0 ≤ (a : ℕ)) => h2 a j ha hle
  have f3 := fun (ha : (a : ℕ) < X.p0) (hj : X.p0 ≤ (j : ℕ)) => h3 a j ha hj
  unfold coefR Dsg sgn
  split_ifs <;> first
    | (exfalso; omega)
    | (norm_num <;> (first | linarith [f1 (by omega)] | linarith [f2 (by omega)] | linarith [f3 (by omega) (by omega)]))

theorem affine_nonneg (α β t t1 : ℝ) (h0 : 0 ≤ α) (h1 : 0 ≤ α + β * t1) (ht : 0 ≤ t) (ht1 : t ≤ t1) :
    0 ≤ α + β * t := by
  rcases le_total 0 β with hb | hb
  · nlinarith [mul_nonneg hb ht]
  · nlinarith [mul_le_mul_of_nonpos_left ht1 hb]

theorem curvNumStatement_holds : CurvNumStatement (E := E) := by
  intro r X L de Fp T rr η hη hrr hT hL hLde hdom
  refine ⟨fun x0 _ z hz ξ hξ => (curvature_statement_holds r X L x0 z hz).2 hL ξ hξ,
    fun x0 _ z hz ξ hξ => (curvature_statement_holds r X (2 • L - de) x0 z hz).2 hLde ξ hξ, ?_⟩
  intro t ht htT x0 _ z hz ξ
  obtain ⟨b, hb, hgr⟩ := MajorantNormalForms.exists_normal_frame X hz
  have hgram : ∀ τ, gram τ.1 X.Gm (mat (rmul (cpt X x0 z) b) τ) =
      diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := fun τ => (hgr τ).1
  set v : X.Ψ → Fin r → ℝ := fun τ a =>
    ((Fp - kapW X - nd X • L) τ a : ℝ) - t * (rr / 2) * (de τ a : ℝ) - 2 * η * (L τ a : ℝ) with hv

  have ht1 : t ≤ 2 * T / rr := by rw [le_div_iff₀ hrr]; linarith
  have hv0 := hdom 0 (by simp)
  have hv1 := hdom (2 * T / rr) (by simp)
  have hvt : IsDominantR X v := by
    intro τ
    obtain ⟨a0, b0, c0⟩ := hv0 τ
    obtain ⟨a1, b1, c1⟩ := hv1 τ
    have gen : ∀ i j : Fin r,
        (fun τ a => ((Fp - kapW X - nd X • L) τ a : ℝ) - 0 * (rr / 2) * (de τ a : ℝ) - 2 * η * (L τ a : ℝ)) τ j ≤
          (fun τ a => ((Fp - kapW X - nd X • L) τ a : ℝ) - 0 * (rr / 2) * (de τ a : ℝ) - 2 * η * (L τ a : ℝ)) τ i →
        (fun τ a => ((Fp - kapW X - nd X • L) τ a : ℝ) - 2 * T / rr * (rr / 2) * (de τ a : ℝ) -
          2 * η * (L τ a : ℝ)) τ j ≤
          (fun τ a => ((Fp - kapW X - nd X • L) τ a : ℝ) - 2 * T / rr * (rr / 2) * (de τ a : ℝ) -
            2 * η * (L τ a : ℝ)) τ i → v τ j ≤ v τ i := by
      intro i j e0 e1
      simp only at e0 e1
      simp only [hv]
      have h := affine_nonneg
        ((((Fp - kapW X - nd X • L) τ i : ℝ) - 2 * η * (L τ i : ℝ)) -
          (((Fp - kapW X - nd X • L) τ j : ℝ) - 2 * η * (L τ j : ℝ)))
        (-(rr / 2) * ((de τ i : ℝ) - de τ j)) t (2 * T / rr) (by linarith) (by linarith) ht ht1
      linarith
    exact ⟨fun i j hij hj => gen i j (a0 i j hij hj) (a1 i j hij hj),
      fun i j hi hij => gen i j (b0 i j hi hij) (b1 i j hi hij),
      fun i j hi hj => gen j i (c0 i j hi hj) (c1 i j hi hj)⟩
  unfold leviM phla
  rw [levi_formula X L x0 z hz b hb hgram ξ, levi_formula X (Fp - kapW X - nd X • L) x0 z hz b hb hgram ξ,
    levi_formula X de x0 z hz b hb hgram ξ]
  rw [← sub_nonneg]
  have key : (∑ τ, ∑ a : Fin r, ∑ j : Fin r, if (a : ℕ) < j then
        coef X (Fp - kapW X - nd X • L) τ a j * ‖Yd X b z (WithLp.toLp 2 ξ) τ j a‖ ^ 2 else 0) -
      t * (rr / 2) * (∑ τ, ∑ a : Fin r, ∑ j : Fin r, if (a : ℕ) < j then
        coef X de τ a j * ‖Yd X b z (WithLp.toLp 2 ξ) τ j a‖ ^ 2 else 0) -
      2 * η * (∑ τ, ∑ a : Fin r, ∑ j : Fin r, if (a : ℕ) < j then
        coef X L τ a j * ‖Yd X b z (WithLp.toLp 2 ξ) τ j a‖ ^ 2 else 0) =
      ∑ τ, ∑ a : Fin r, ∑ j : Fin r, if (a : ℕ) < j then
        coefR X v τ a j * ‖Yd X b z (WithLp.toLp 2 ξ) τ j a‖ ^ 2 else 0 := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · unfold coef coefR; simp only [hv]; ring
    · ring
  have hnn : 0 ≤ ∑ τ, ∑ a : Fin r, ∑ j : Fin r, if (a : ℕ) < j then
      coefR X v τ a j * ‖Yd X b z (WithLp.toLp 2 ξ) τ j a‖ ^ 2 else 0 :=
    Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun j _ => by
      split_ifs with h
      · exact mul_nonneg (coefR_nonneg X v hvt τ a j h) (sq_nonneg _)
      · exact le_rfl
  linarith

end ReciprocityTheory.ChartRestriction.G.AR.Up
end
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUB

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal ContDiff

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  {x1' : Frame X.Ψ r} (b1 : Frame X.Ψ r) (D : ExtFPf.LUData X x1')

theorem cpt_diff (x : Frame X.Ψ r) : Differentiable ℂ (cpt X x) := by
  exact (OntoB.cd_cpt X x).differentiable (by simp)

def Uc : Set (V (nd X)) := (cpt X (rmul x1' b1)) ⁻¹' ExtFPf.cell D

theorem isOpen_Uc : IsOpen (Uc X b1 D) := by
  have hcell : IsOpen (ExtFPf.cell D) :=
    (FourierCoefficientDomain.isOpen_dom (X := X)).inter (D.hΔ.continuous.isOpen_preimage _ isOpen_compl_singleton)
  exact (cpt_diff X _).continuous.isOpen_preimage _ hcell

theorem Φ_diffOn : DifferentiableOn ℂ (Φ X b1 D) (Uc X b1 D) := by
  exact D.hz.comp (cpt_diff X _).differentiableOn fun z hz => hz

theorem Φ_cdOn : ContDiffOn ℂ ∞ (Φ X b1 D) (Uc X b1 D) := by
  refine contDiffOn_piLp' 2 fun i => ?_
  have hi : DifferentiableOn ℂ (fun x => (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin (nd X)) i) (Φ X b1 D x))
      (Uc X b1 D) :=
    (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin (nd X)) i).differentiable.comp_differentiableOn (Φ_diffOn X b1 D)
  exact ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn (nd X) _ _ (isOpen_Uc X b1 D) hi

theorem jac_bound {ρ0 : ℝ} (hsub : Metric.closedBall (0 : V (nd X)) ρ0 ⊆ Uc X b1 D) :
    ∃ Kj : ℝ, ∀ z ∈ Metric.closedBall (0 : V (nd X)) ρ0, |(fderiv ℝ (Φ X b1 D) z).det| ≤ Kj := by
  have hcd : ContDiffOn ℝ ∞ (Φ X b1 D) (Uc X b1 D) := (Φ_cdOn X b1 D).restrict_scalars ℝ
  have hfd : ContinuousOn (fun z => fderiv ℝ (Φ X b1 D) z) (Uc X b1 D) :=
    hcd.continuousOn_fderiv_of_isOpen (isOpen_Uc X b1 D) (by simp)
  have hdet : ContinuousOn (fun z => (fderiv ℝ (Φ X b1 D) z).det) (Uc X b1 D) :=
    ContinuousLinearMap.continuous_det.comp_continuousOn hfd
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : V (nd X)) ρ0).exists_bound_of_continuousOn (hdet.mono hsub)
  exact ⟨C, fun z hz => by simpa [Real.norm_eq_abs] using hC z hz⟩

theorem dens_bound {ρ0 : ℝ} (hsub : Metric.closedBall (0 : V (nd X)) ρ0 ⊆ Uc X b1 D) :
    ∃ Kd : ℝ, ∀ z ∈ Metric.closedBall (0 : V (nd X)) ρ0, densF X x1' (Φ X b1 D z) ≤ Kd := by
  have hΦc : ContinuousOn (Φ X b1 D) (Uc X b1 D) := (Φ_diffOn X b1 D).continuousOn
  have hmaps : Set.MapsTo (Φ X b1 D) (Uc X b1 D) (OmF X x1') := fun z hz => (split X b1 D hz).1
  have hc : ContinuousOn (fun z => densF X x1' (Φ X b1 D z)) (Uc X b1 D) :=
    (OntoB.densF_continuousOn (X := X) (x0 := x1')).comp hΦc hmaps
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : V (nd X)) ρ0).exists_bound_of_continuousOn (hc.mono hsub)
  exact ⟨C, fun z hz => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC z hz)⟩

def Tset (x1 : Frame X.Ψ r) (ρ : ℝ) : Set (Frame X.Ψ r) :=
  (fun p : V (nd X) × Frame X.Ψ r => rmul (cpt X x1 p.1) p.2) '' (Metric.ball 0 ρ ×ˢ Bor X.Ψ r)

theorem Tset_eq {ρ : ℝ} (hsub : Metric.ball (0 : V (nd X)) ρ ⊆ Uc X b1 D) :
    Tset X (rmul x1' b1) ρ = KU.Sset X x1' (Φ X b1 D '' Metric.ball 0 ρ) := by
  have hTmem : ∀ {y c : Frame X.Ψ r}, c ∈ Bor X.Ψ r →
      (rmul y c ∈ Tset X (rmul x1' b1) ρ ↔ y ∈ Tset X (rmul x1' b1) ρ) := fun hc =>
    KU.rmul_mem_S X (x0 := rmul x1' b1) (FF := Metric.ball 0 ρ) hc
  ext y
  constructor
  · rintro ⟨⟨z, b⟩, ⟨hz, hb⟩, rfl⟩
    have hs := split X b1 D (hsub hz)
    show rmul (cpt X (rmul x1' b1) z) b ∈ _
    rw [KU.rmul_mem_S X hb, hs.2.2]
    exact ⟨(Φ X b1 D z, β X b1 D z), ⟨⟨z, hz, rfl⟩, hs.2.1⟩, rfl⟩
  · rintro ⟨⟨w, b⟩, ⟨⟨z, hz, rfl⟩, hb⟩, rfl⟩
    have hs := split X b1 D (hsub hz)
    show rmul (cpt X x1' (Φ X b1 D z)) b ∈ Tset X (rmul x1' b1) ρ
    rw [hTmem hb, ← MI.rmul_invF X (y := cpt X x1' (Φ X b1 D z)) hs.2.1, ← hs.2.2,
      hTmem (MI.invF_mem' X hs.2.1)]
    exact ⟨(z, ExtFPf.oneF X), ⟨hz, ExtFPf.oneF_mem X⟩, ExtFPf.rmul_oneF X _⟩

theorem meas_image {ρ : ℝ} (hsub : Metric.ball (0 : V (nd X)) ρ ⊆ Uc X b1 D) (hx1 : rmul x1' b1 ∈ X.dom) :
    MeasurableSet (Φ X b1 D '' Metric.ball 0 ρ) := by
  exact measurableSet_ball.image_of_continuousOn_injOn ((Φ_diffOn X b1 D).continuousOn.mono hsub)
    ((Φ_injOn X b1 D hx1).mono hsub)

theorem meas_Tset (ho' : IsOrth X x1') {ρ : ℝ} (hsub : Metric.ball (0 : V (nd X)) ρ ⊆ Uc X b1 D)
    (hx1 : rmul x1' b1 ∈ X.dom) : MeasurableSet (Tset X (rmul x1' b1) ρ) := by
  rw [Tset_eq X b1 D hsub]
  exact KU.meas_S X ho' (meas_image X b1 D hsub hx1)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
end
