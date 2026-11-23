module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfP
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle024
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle028
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfH

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD

theorem FrameMeasStatement_holds {E : Type} [Field E] [NumberField E] [IsCMField E] :
    FrameMeasStatement (E := E) :=
  @GlobalTheory.FrameMeasureClosed.frameMeas_holds E _ _ _

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField Complex Matrix Topology Filter MeasureTheory Set ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB ReciprocityTheory.ChartRestriction.G.AR.Up.OntoH
  ReciprocityTheory.ChartRestriction.G.AR.Up.OntoI
open scoped ComplexConjugate ContDiff ENNReal InnerProductSpace

noncomputable section

namespace OntoJ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def Dt (X : Data E r) (x0 : Frame X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (la : Wt X.Ψ r)
    (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ) : Prop :=
  DifferentiableOn ℂ F (OmF X x0) ∧ InAt X x0 W bb F ∧ IsBEq X la P ∧
    ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z


open Classical in
def TL {α : Type*} [MeasurableSpace α] (ν : Measure α) (f : α → ℂ) : Lp ℂ 2 ν :=
  if h : MemLp f 2 ν then h.toLp f else 0

section TLs

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}

theorem TL_eq {f : α → ℂ} (h : MemLp f 2 ν) : TL ν f = h.toLp f := by
  unfold TL
  rw [dite_eq_left h]

theorem TL_congr {f g : α → ℂ} (hf : MemLp f 2 ν) (hfg : f =ᵐ[ν] g) : TL ν f = TL ν g := by
  rw [TL_eq hf, TL_eq (hf.ae_eq hfg)]
  exact (MemLp.toLp_eq_toLp_iff _ _).2 hfg

theorem TL_add {f g : α → ℂ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    TL ν (f + g) = TL ν f + TL ν g := by
  rw [TL_eq (hf.add hg), TL_eq hf, TL_eq hg]
  exact MemLp.toLp_add hf hg

theorem TL_sub {f g : α → ℂ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    TL ν (f - g) = TL ν f - TL ν g := by
  rw [TL_eq (hf.sub hg), TL_eq hf, TL_eq hg]
  exact MemLp.toLp_sub hf hg

theorem TL_smul {f : α → ℂ} (a : ℂ) (hf : MemLp f 2 ν) : TL ν (a • f) = a • TL ν f := by
  rw [TL_eq (hf.const_smul a), TL_eq hf]
  exact MemLp.toLp_const_smul a hf

theorem TL_zero : TL ν (0 : α → ℂ) = 0 := by
  rw [TL_eq MeasureTheory.MemLp.zero]
  exact MemLp.toLp_zero _

end TLs

variable (X : Data E r) (x0 : Frame X.Ψ r) {W : Frame X.Ψ r → ℝ≥0∞} {bb : ℝ} {la : Wt X.Ψ r}

theorem ka_cont : ContinuousOn (kaF X x0 bb) (OmF X x0) :=
  fun _ hz => (ka_contDiffAt bb hz).continuousAt.continuousWithinAt

theorem aemF (hWm : Measurable W) {F : V (nd X) → ℂ} (hF : ContinuousOn F (OmF X x0)) :
    AEMeasurable (fun z => ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z)) (muF X x0) := by
  have h1 : ContinuousOn (fun z => ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z)) (OmF X x0) :=
    ENNReal.continuous_ofReal.comp_continuousOn
      ((hF.norm.pow 2).div (ka_cont X x0) fun z _ => (Real.exp_pos _).ne')
  have h2 : Measurable fun z => W (cpt X x0 z) := hWm.comp (cd_cpt X x0).continuous.measurable
  have h3 : AEMeasurable (fun z => ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z))
      (volume.restrict (OmF X x0)) :=
    (h1.aemeasurable (isOpen_OmF X x0).measurableSet).mul h2.aemeasurable
  exact h3.mono_ac (withDensity_absolutelyContinuous _ _)

theorem Dt_zero : Dt X x0 W bb la (fun _ => 0) (fun _ => 0) := by
  refine ⟨differentiableOn_const _, ?_, ⟨differentiableOn_const _, fun _ _ _ _ => by simp⟩, fun _ _ => rfl⟩
  unfold InAt
  simp

theorem Dt_add (hWm : Measurable W) {F1 F2 : V (nd X) → ℂ} {P1 P2 : Frame X.Ψ r → ℂ}
    (h1 : Dt X x0 W bb la F1 P1) (h2 : Dt X x0 W bb la F2 P2) :
    Dt X x0 W bb la (fun z => F1 z + F2 z) (fun y => P1 y + P2 y) := by
  refine ⟨h1.1.add h2.1, ?_, ⟨h1.2.2.1.1.add h2.2.2.1.1, fun x hx b hb => ?_⟩, fun z hz => ?_⟩
  · unfold InAt
    refine lt_of_le_of_lt (lint_add_le (k := kaF X x0 bb) (fun z => Real.exp_pos _)
      (aemF X x0 hWm h1.1.continuousOn)) ?_
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) h1.2.1, ENNReal.mul_lt_top (by simp) h2.2.1⟩
  · beta_reduce
    rw [h1.2.2.1.2 x hx b hb, h2.2.2.1.2 x hx b hb]
    ring
  · beta_reduce
    rw [h1.2.2.2 z hz, h2.2.2.2 z hz]

theorem Dt_smul (a : ℂ) {F : V (nd X) → ℂ} {P : Frame X.Ψ r → ℂ} (h : Dt X x0 W bb la F P) :
    Dt X x0 W bb la (fun z => a * F z) (fun y => a * P y) := by
  refine ⟨h.1.const_mul a, ?_, ⟨h.2.2.1.1.const_mul a, fun x hx b hb => ?_⟩, fun z hz => ?_⟩
  · have heq : ∀ z, ENNReal.ofReal (‖a * F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z) =
        ENNReal.ofReal (‖a‖ ^ 2) * (ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z)) := by
      intro z
      rw [norm_mul, mul_pow, mul_div_assoc, ENNReal.ofReal_mul (by positivity), mul_assoc]
    unfold InAt
    simp_rw [heq]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h.2.1
  · beta_reduce
    rw [h.2.2.1.2 x hx b hb]
    ring
  · beta_reduce
    rw [h.2.2.2 z hz]

end OntoJ

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
  Metric
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem nsq_eq_normSq (s : Fin (nd X) → Frame X.Ψ r → ℂ) (x0 : Frame X.Ψ r) (z : V (nd X)) :
    (∑ k, ‖s k (cpt X x0 z)‖ ^ 2) = HE.nsq (fun k z => s k (cpt X x0 z)) z := by
  unfold HE.nsq
  exact Finset.sum_congr rfl fun k _ => (Complex.normSq_eq_norm_sq _).symm

theorem lhs_finite (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (Xa : ArchInM X) (Fl : FlatM X Xa)
    (ψ : Frame X.Ψ r → ℝ) (C0 : ℝ) (hψb : ∀ x ∈ X.dom, ψ x ≤ C0) (bb : ℝ) (hbb : 0 ≤ bb)
    (ε : ℝ) (hε : 0 < ε)
    (hnull : volume {y | y ∈ OmF X x0 ∧ HE.nsq (fun k z => Fl.s k (cpt X x0 z)) y = 0} = 0)
    (F : V (nd X) → ℂ)
    (hI : ∫⁻ y in OmF X x0, ENNReal.ofReal (‖HE.cut ε hε y - F y‖ ^ 2 *
          Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb y) *
          HE.nsq (fun k z => Fl.s k (cpt X x0 z)) y ^ (-(nd X : ℝ))) < ⊤)
    (P : Frame X.Ψ r → ℂ) (hPF : ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) (N : Set (Frame X.Ψ r))
    (hN2 : ∀ z ∈ OmF X x0, cpt X x0 z ∈ N → z ∉ closedBall (0 : V (nd X)) (2 * ε)) :
    ∫⁻ z, N.indicator (gφ X P Xa.Fp Xa.L Fl.s) (cpt X x0 z) ∂muF X x0 < ⊤ := by
  rw [muF_lintegral]
  have hO := ExF.isOpen_OmF X x0
  have hpt : ∀ᵐ z ∂(volume.restrict (OmF X x0)),
      ENNReal.ofReal (densF X x0 z) * N.indicator (gφ X P Xa.Fp Xa.L Fl.s) (cpt X x0 z) ≤
        ENNReal.ofReal (Real.exp C0) * ENNReal.ofReal (‖HE.cut ε hε z - F z‖ ^ 2 *
          Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb z) *
          HE.nsq (fun k z => Fl.s k (cpt X x0 z)) z ^ (-(nd X : ℝ))) := by
    rw [ae_restrict_iff' hO.measurableSet]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with z hz0 hz
    by_cases hzN : cpt X x0 z ∈ N
    swap
    · rw [Set.indicator_of_notMem hzN, mul_zero]; exact zero_le
    rw [Set.indicator_of_mem hzN]
    have hx : cpt X x0 z ∈ X.dom := hz
    have hN : 0 < HE.nsq (fun k z => Fl.s k (cpt X x0 z)) z := by
      rcases (HE.nsq_nonneg _ z).lt_or_eq with h | h
      · exact h
      · exact absurd ⟨hz, h.symm⟩ hz0
    have hcut : HE.cut ε hε z = 0 := HE.cut_zero ε hε (by
      have := hN2 z hz hzN
      rw [mem_closedBall, dist_zero_right, not_le] at this; exact this.le)
    set S := ∑ k, X.pnorm Xa.L (Fl.s k) (cpt X x0 z) ^ 2 with hSdef
    have hS : S = HE.nsq (fun k z => Fl.s k (cpt X x0 z)) z * Real.exp (-phla X Xa.L (cpt X x0 z)) :=
      pnorm_sum_eq X Xa.L Fl.s hx
    have hSpos : 0 < S := by rw [hS]; positivity
    have hrho := rhoF_eq X x0 Xa.Fp Xa.L ψ bb Fl.s hz hN
    rw [← hSdef] at hrho
    rw [gφ_dom X P Xa.Fp Xa.L Fl.s hx, ← hSdef, ← ENNReal.ofReal_inv_of_pos hSpos,
      ← ENNReal.ofReal_pow (inv_nonneg.2 hSpos.le), ← mul_assoc,
      ← ENNReal.ofReal_mul (densF_pos X x0 hz).le,
      ← ENNReal.ofReal_mul (mul_nonneg (densF_pos X x0 hz).le (by positivity)),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    rw [hPF z hz, hcut, zero_sub, norm_neg]
    have hd := densF_pos X x0 hz
    have hrho2 : rhoF X x0 Xa.Fp ψ bb z = Real.exp (-phla X Xa.Fp (cpt X x0 z)) *
        Real.exp (-ψ (cpt X x0 z)) * Real.exp (bb * rhF X x0 z) * densF X x0 z := by
      rw [rhoF, Real.exp_add, Real.exp_add, Real.exp_log hd, neg_add, Real.exp_add]
    have hSn : S⁻¹ ^ (nd X) = (S ^ (nd X : ℝ))⁻¹ := by
      rw [Real.rpow_natCast, inv_pow]
    have hSn0 : 0 < S ^ (nd X : ℝ) := Real.rpow_pos_of_pos hSpos _
    set A := Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb z) *
      HE.nsq (fun k z => Fl.s k (cpt X x0 z)) z ^ (-(nd X : ℝ)) with hAdef
    have hA0 : 0 ≤ A := by positivity

    have key : densF X x0 z * Real.exp (-phla X Xa.Fp (cpt X x0 z)) * S⁻¹ ^ (nd X) =
        A * Real.exp (ψ (cpt X x0 z)) * Real.exp (-(bb * rhF X x0 z)) := by
      have e1 : A = rhoF X x0 Xa.Fp ψ bb z / S ^ (nd X : ℝ) := by
        rw [hrho]; field_simp
      rw [e1, hrho2, hSn]
      have h1 : Real.exp (-ψ (cpt X x0 z)) * Real.exp (ψ (cpt X x0 z)) = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      have h2 : Real.exp (bb * rhF X x0 z) * Real.exp (-(bb * rhF X x0 z)) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      field_simp
      nlinarith [h1, h2]
    have hle : A * Real.exp (ψ (cpt X x0 z)) * Real.exp (-(bb * rhF X x0 z)) ≤ Real.exp C0 * A := by
      have e2 : Real.exp (ψ (cpt X x0 z)) ≤ Real.exp C0 := Real.exp_le_exp.2 (hψb _ hx)
      have e3 : Real.exp (-(bb * rhF X x0 z)) ≤ 1 := by
        rw [Real.exp_le_one_iff, neg_nonpos]
        exact mul_nonneg hbb (ExF.rhF_nonneg X x0 ho hz)
      have e4 := (Real.exp_pos (-(bb * rhF X x0 z))).le
      calc A * Real.exp (ψ (cpt X x0 z)) * Real.exp (-(bb * rhF X x0 z))
          ≤ A * Real.exp C0 * 1 := by gcongr
        _ = Real.exp C0 * A := by ring
    have hF2 : 0 ≤ ‖F z‖ ^ 2 := sq_nonneg _
    calc densF X x0 z * (‖F z‖ ^ 2 * Real.exp (-phla X Xa.Fp (cpt X x0 z))) * S⁻¹ ^ (nd X)
        = ‖F z‖ ^ 2 * (densF X x0 z * Real.exp (-phla X Xa.Fp (cpt X x0 z)) * S⁻¹ ^ (nd X)) := by ring
      _ ≤ ‖F z‖ ^ 2 * (Real.exp C0 * A) := by rw [key]; exact mul_le_mul_of_nonneg_left hle hF2
      _ = Real.exp C0 * (‖F z‖ ^ 2 * Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb z) *
            HE.nsq (fun k z => Fl.s k (cpt X x0 z)) z ^ (-(nd X : ℝ))) := by rw [hAdef]; ring
  calc ∫⁻ z in OmF X x0, ENNReal.ofReal (densF X x0 z) * N.indicator (gφ X P Xa.Fp Xa.L Fl.s) (cpt X x0 z)
      ≤ ∫⁻ z in OmF X x0, ENNReal.ofReal (Real.exp C0) * ENNReal.ofReal (‖HE.cut ε hε z - F z‖ ^ 2 *
          Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb z) *
          HE.nsq (fun k z => Fl.s k (cpt X x0 z)) z ^ (-(nd X : ℝ))) := lintegral_mono_ae hpt
    _ = ENNReal.ofReal (Real.exp C0) * ∫⁻ z in OmF X x0, ENNReal.ofReal (‖HE.cut ε hε z - F z‖ ^ 2 *
          Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb z) *
          HE.nsq (fun k z => Fl.s k (cpt X x0 z)) z ^ (-(nd X : ℝ))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI

theorem rhs_bound (x1 : Frame X.Ψ r) (Xa : ArchInM X) (Fl : FlatM X Xa) (P : Frame X.Ψ r → ℂ)
    (N : Set (Frame X.Ψ r)) (ρ1 : ℝ) (hρ1 : 0 < ρ1) (hcb : closedBall (0 : V (nd X)) ρ1 ⊆ OmF X x1)
    (hN1 : ∀ w ∈ ball (0 : V (nd X)) ρ1, cpt X x1 w ∈ N) :
    ∃ c1 : ℝ, 0 < c1 ∧ ENNReal.ofReal c1 * ∫⁻ w in ball (0 : V (nd X)) ρ1,
      ENNReal.ofReal (‖P (cpt X x1 w)‖ ^ 2 * (∑ k, ‖Fl.s k (cpt X x1 w)‖ ^ 2) ^ (-(nd X : ℝ))) ≤
      ∫⁻ w, N.indicator (gφ X P Xa.Fp Xa.L Fl.s) (cpt X x1 w) ∂muF X x1 := by
  set h1 : V (nd X) → ℝ := fun w => Real.exp (Real.log (densF X x1 w) - phla X Xa.Fp (cpt X x1 w) +
    (nd X : ℝ) * phla X Xa.L (cpt X x1 w)) with hh1
  have hc : ContinuousOn h1 (closedBall (0 : V (nd X)) ρ1) := fun w hw =>
    (Real.continuous_exp.continuousAt.comp ((((logDens_cdAt X x1 (hcb hw)).sub
      (phla_cpt_cdAt X x1 (hcb hw) Xa.Fp)).add (contDiffAt_const.mul
        (phla_cpt_cdAt X x1 (hcb hw) Xa.L))).continuousAt)).continuousWithinAt
  obtain ⟨w0, hw0, hmin⟩ := (isCompact_closedBall (0 : V (nd X)) ρ1).exists_isMinOn
    ⟨0, mem_closedBall_self hρ1.le⟩ hc
  refine ⟨h1 w0, Real.exp_pos _, ?_⟩
  have hpt : ∀ w ∈ ball (0 : V (nd X)) ρ1, ENNReal.ofReal (h1 w0) *
      ENNReal.ofReal (‖P (cpt X x1 w)‖ ^ 2 * (∑ k, ‖Fl.s k (cpt X x1 w)‖ ^ 2) ^ (-(nd X : ℝ))) ≤
      ENNReal.ofReal (densF X x1 w) * N.indicator (gφ X P Xa.Fp Xa.L Fl.s) (cpt X x1 w) := by
    intro w hw
    have hwO := hcb (ball_subset_closedBall hw)
    have hx : cpt X x1 w ∈ X.dom := hwO
    rw [Set.indicator_of_mem (hN1 w hw), gφ_dom X P Xa.Fp Xa.L Fl.s hx, nsq_eq_normSq]
    set n2 := HE.nsq (fun k z => Fl.s k (cpt X x1 z)) w with hn2
    rcases (HE.nsq_nonneg (fun k z => Fl.s k (cpt X x1 z)) w).lt_or_eq with hN | hN
    · have hN' : 0 < n2 := hN
      set S := ∑ k, X.pnorm Xa.L (Fl.s k) (cpt X x1 w) ^ 2 with hSdef
      have hS : S = n2 * Real.exp (-phla X Xa.L (cpt X x1 w)) := pnorm_sum_eq X Xa.L Fl.s hx
      have hSpos : 0 < S := by rw [hS]; positivity
      have hd := densF_pos X x1 hwO
      rw [← ENNReal.ofReal_inv_of_pos hSpos, ← ENNReal.ofReal_pow (inv_nonneg.2 hSpos.le), ← mul_assoc,
        ← ENNReal.ofReal_mul hd.le, ← ENNReal.ofReal_mul (mul_nonneg hd.le (by positivity)),
        ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      apply ENNReal.ofReal_le_ofReal
      have hid : densF X x1 w * Real.exp (-phla X Xa.Fp (cpt X x1 w)) * S⁻¹ ^ (nd X) =
          h1 w * n2 ^ (-(nd X : ℝ)) := by
        have e1 : h1 w = densF X x1 w * Real.exp (-phla X Xa.Fp (cpt X x1 w)) *
            Real.exp (phla X Xa.L (cpt X x1 w)) ^ (nd X) := by
          simp only [hh1]
          rw [Real.exp_add, Real.exp_sub, Real.exp_log hd, Real.exp_neg, Real.exp_nat_mul]
          ring
        rw [e1, hS, Real.rpow_neg hN'.le, Real.rpow_natCast, mul_inv, mul_pow,
          show (Real.exp (-phla X Xa.L (cpt X x1 w)))⁻¹ = Real.exp (phla X Xa.L (cpt X x1 w)) by
            rw [Real.exp_neg, inv_inv], inv_pow]
        ring
      have hm : h1 w0 ≤ h1 w := hmin (ball_subset_closedBall hw)
      have hq : 0 ≤ ‖P (cpt X x1 w)‖ ^ 2 * n2 ^ (-(nd X : ℝ)) := by positivity
      calc h1 w0 * (‖P (cpt X x1 w)‖ ^ 2 * n2 ^ (-(nd X : ℝ)))
          ≤ h1 w * (‖P (cpt X x1 w)‖ ^ 2 * n2 ^ (-(nd X : ℝ))) := mul_le_mul_of_nonneg_right hm hq
        _ = densF X x1 w * (‖P (cpt X x1 w)‖ ^ 2 * Real.exp (-phla X Xa.Fp (cpt X x1 w))) *
              S⁻¹ ^ (nd X) := by
            rw [show densF X x1 w * (‖P (cpt X x1 w)‖ ^ 2 * Real.exp (-phla X Xa.Fp (cpt X x1 w))) *
              S⁻¹ ^ (nd X) = ‖P (cpt X x1 w)‖ ^ 2 * (densF X x1 w * Real.exp (-phla X Xa.Fp (cpt X x1 w)) *
              S⁻¹ ^ (nd X)) by ring, hid]
            ring
    · have hN' : n2 = 0 := hN.symm
      rw [hN', Real.zero_rpow (by have := Xa.n_ge; simp; omega), mul_zero, ENNReal.ofReal_zero,
        mul_zero]
      exact zero_le
  calc ENNReal.ofReal (h1 w0) * ∫⁻ w in ball (0 : V (nd X)) ρ1,
        ENNReal.ofReal (‖P (cpt X x1 w)‖ ^ 2 * (∑ k, ‖Fl.s k (cpt X x1 w)‖ ^ 2) ^ (-(nd X : ℝ)))
      = ∫⁻ w in ball (0 : V (nd X)) ρ1, ENNReal.ofReal (h1 w0) *
        ENNReal.ofReal (‖P (cpt X x1 w)‖ ^ 2 * (∑ k, ‖Fl.s k (cpt X x1 w)‖ ^ 2) ^ (-(nd X : ℝ))) :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ w in ball (0 : V (nd X)) ρ1, ENNReal.ofReal (densF X x1 w) *
          N.indicator (gφ X P Xa.Fp Xa.L Fl.s) (cpt X x1 w) := setLIntegral_mono' measurableSet_ball hpt
    _ ≤ ∫⁻ w in OmF X x1, ENNReal.ofReal (densF X x1 w) *
          N.indicator (gφ X P Xa.Fp Xa.L Fl.s) (cpt X x1 w) :=
        lintegral_mono_set (ball_subset_closedBall.trans hcb)
    _ = _ := (muF_lintegral X x1 _).symm

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
end
