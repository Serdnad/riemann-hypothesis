module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle150
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwoC

open MeasureTheory

def lg (t : ℝ) : ℝ := Real.log ‖(t : ℂ) + I‖

theorem tI_ne (t : ℝ) : (t : ℂ) + I ≠ 0 := by
  intro h; have := congrArg Complex.im h; simp at this

theorem sq_norm_tI (t : ℝ) : ‖(t : ℂ) + I‖ ^ 2 = 1 + ‖t‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Real.norm_eq_abs, sq_abs]; simp; ring

theorem norm_tI_eq (t : ℝ) : ‖(t : ℂ) + I‖ = Real.exp (lg t) :=
  (Real.exp_log (norm_pos_iff.2 (tI_ne t))).symm

theorem lg_nonneg (t : ℝ) : 0 ≤ lg t := by
  apply Real.log_nonneg
  have h := sq_norm_tI t
  nlinarith [norm_nonneg ((t : ℂ) + I), sq_nonneg ‖t‖]

theorem continuous_lg : Continuous lg := by
  unfold lg
  exact (Continuous.norm (by fun_prop)).log (fun t => (norm_pos_iff.2 (tI_ne t)).ne')

def G (σ : ℂ) (t : ℝ) : ℂ := ((t : ℂ) + I)⁻¹ ^ 2 * Complex.exp ((lg t : ℂ) * (-2 * σ))

def G' (σ : ℂ) (t : ℝ) : ℂ :=
  ((t : ℂ) + I)⁻¹ ^ 2 * (Complex.exp ((lg t : ℂ) * (-2 * σ)) * ((lg t : ℂ) * (-2)))

theorem cConst_eq : cConst = fun σ => ∫ t, G σ t := by
  funext σ
  unfold cConst hTrans G
  congr 1; funext t
  simp only [ofReal_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one, ofReal_one, one_mul]
  unfold phi
  congr 1
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (norm_pos_iff.2 (tI_ne t)).ne'),
    ← Complex.ofReal_log (norm_nonneg _)]
  rfl

theorem norm_G (σ : ℂ) (t : ℝ) : ‖G σ t‖ = Real.exp (-(2 + 2 * σ.re) * lg t) := by
  unfold G
  rw [norm_mul, norm_pow, norm_inv, norm_tI_eq, Complex.norm_exp, ← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  simp
  ring

theorem norm_G' (σ : ℂ) (t : ℝ) : ‖G' σ t‖ = Real.exp (-(2 + 2 * σ.re) * lg t) * (2 * lg t) := by
  have : G' σ t = G σ t * ((lg t : ℂ) * (-2)) := by unfold G G'; ring
  rw [this, norm_mul, norm_G, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (lg_nonneg t)]
  simp; ring

theorem bound_G {ε : ℝ} (hε : 0 < ε) {σ : ℂ} (hσ : -1 / 2 + ε ≤ σ.re) (t : ℝ) :
    ‖G σ t‖ ≤ Real.exp (-(1 + ε) * lg t) := by
  rw [norm_G]
  apply Real.exp_le_exp.2
  have := lg_nonneg t
  nlinarith

theorem bound_G' {ε : ℝ} (hε : 0 < ε) {σ : ℂ} (hσ : -1 / 2 + ε ≤ σ.re) (t : ℝ) :
    ‖G' σ t‖ ≤ 2 / ε * Real.exp (-(1 + ε) * lg t) := by
  rw [norm_G']
  have hL := lg_nonneg t
  have h1 : Real.exp (-(2 + 2 * σ.re) * lg t) ≤ Real.exp (-(1 + ε) * lg t) * Real.exp (-(ε * lg t)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith
  have h2 : ε * lg t + 1 ≤ Real.exp (ε * lg t) := Real.add_one_le_exp _
  have h3 : Real.exp (-(ε * lg t)) * (2 * lg t) ≤ 2 / ε := by
    rw [Real.exp_neg, le_div_iff₀ hε]
    have hp := Real.exp_pos (ε * lg t)
    rw [show (Real.exp (ε * lg t))⁻¹ * (2 * lg t) * ε = 2 * (ε * lg t) / Real.exp (ε * lg t) by field_simp]
    rw [div_le_iff₀ hp]
    linarith
  calc Real.exp (-(2 + 2 * σ.re) * lg t) * (2 * lg t)
      ≤ Real.exp (-(1 + ε) * lg t) * Real.exp (-(ε * lg t)) * (2 * lg t) :=
        mul_le_mul_of_nonneg_right h1 (by linarith)
    _ = Real.exp (-(1 + ε) * lg t) * (Real.exp (-(ε * lg t)) * (2 * lg t)) := by ring
    _ ≤ Real.exp (-(1 + ε) * lg t) * (2 / ε) := mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = 2 / ε * Real.exp (-(1 + ε) * lg t) := by ring

theorem integrable_expL {ε : ℝ} (hε : 0 < ε) : Integrable (fun t : ℝ => Real.exp (-(1 + ε) * lg t)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 1 + ε) (by simp; linarith)
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [← sq_norm_tI, norm_tI_eq, ← Real.exp_nat_mul, ← Real.exp_mul]
  congr 1; push_cast; ring

theorem hasDerivAt_G (σ : ℂ) (t : ℝ) : HasDerivAt (fun s => G s t) (G' σ t) σ := by
  unfold G G'
  have h : HasDerivAt (fun s : ℂ => (lg t : ℂ) * (-2 * s)) ((lg t : ℂ) * (-2)) σ := by
    exact (((hasDerivAt_id σ).const_mul (-2 : ℂ)).const_mul (lg t : ℂ)).congr_deriv (by ring)
  exact h.cexp.const_mul _

theorem continuous_G (σ : ℂ) : Continuous (G σ) := by
  unfold G
  have : Continuous fun t : ℝ => ((t : ℂ) + I)⁻¹ :=
    (by fun_prop : Continuous fun t : ℝ => (t : ℂ) + I).inv₀ tI_ne
  exact (this.pow 2).mul (Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp continuous_lg).mul continuous_const))

theorem continuous_G' (σ : ℂ) : Continuous (G' σ) := by
  have : G' σ = fun t => G σ t * ((lg t : ℂ) * (-2)) := by funext t; unfold G G'; ring
  rw [this]
  exact (continuous_G σ).mul ((Complex.continuous_ofReal.comp continuous_lg).mul continuous_const)

end GlobalTheory.HeckeTwoC

namespace GlobalTheory.HeckeTwo

open MeasureTheory GlobalTheory.HeckeTwoC

theorem cConst_differentiableOn : DifferentiableOn ℂ cConst halfPlane := by
  rw [cConst_eq]
  intro σ₀ hσ₀
  have hre : -1 / 2 < σ₀.re := hσ₀
  set ε := (σ₀.re + 1 / 2) / 2 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  have hball : ∀ σ ∈ Metric.ball σ₀ ε, -1 / 2 + ε ≤ σ.re := by
    intro σ hσ
    have h1 : |(σ - σ₀).re| ≤ ‖σ - σ₀‖ := Complex.abs_re_le_norm _
    have h2 : ‖σ - σ₀‖ < ε := by simpa [dist_eq_norm] using hσ
    have h3 := (abs_lt.1 (lt_of_le_of_lt h1 h2)).1
    simp only [sub_re] at h3
    linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := G) (F' := G')
    (x₀ := σ₀) (bound := fun t => 2 / ε * Real.exp (-(1 + ε) * lg t))
    (Metric.ball_mem_nhds σ₀ hε)
    (Filter.Eventually.of_forall fun σ => (continuous_G σ).aestronglyMeasurable)
    ((integrable_expL hε).mono' (continuous_G σ₀).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => bound_G hε (hball σ₀ (Metric.mem_ball_self hε)) t))
    (continuous_G' σ₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t σ hσ => bound_G' hε (hball σ hσ) t)
    ((integrable_expL hε).const_mul _)
    (Filter.Eventually.of_forall fun t σ _ => hasDerivAt_G σ t)
  exact key.2.differentiableAt.differentiableWithinAt

end GlobalTheory.HeckeTwo
end
end

section

open NumberField Complex MeasureTheory

namespace GlobalTheory.HeckeTwo.PhiLine

theorem norm_line_sq (t y : ℝ) : ‖((t : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 = t ^ 2 + y ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp; ring

theorem abs_le_norm_line (t y : ℝ) : |y| ≤ ‖((t : ℂ) + (y : ℂ) * Complex.I)‖ := by
  have := Complex.abs_im_le_norm ((t : ℂ) + (y : ℂ) * Complex.I)
  simpa using this

theorem line_ne_zero (t y : ℝ) (hy : y ≠ 0) : ((t : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hy this

theorem norm_phi_le (σ : ℂ) (hσ : 0 < σ.re) (y : ℝ) (hy : y ≠ 0) (t : ℝ) :
    ‖GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      |y| ^ (-2 * σ.re) * (min 1 (y ^ 2))⁻¹ * (1 + t ^ 2)⁻¹ := by
  set w : ℂ := (t : ℂ) + (y : ℂ) * Complex.I with hw
  have hay : 0 < |y| := abs_pos.2 hy
  have hle : |y| ≤ ‖w‖ := abs_le_norm_line t y
  have hpos : 0 < ‖w‖ := lt_of_lt_of_le hay hle
  have hsq : ‖w‖ ^ 2 = t ^ 2 + y ^ 2 := norm_line_sq t y
  unfold GlobalTheory.HeckeTwo.phi
  rw [norm_mul, norm_pow, norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  have hre : (-2 * σ).re = -2 * σ.re := by simp
  rw [hre]
  have h1 : ‖w‖ ^ (-2 * σ.re) ≤ |y| ^ (-2 * σ.re) :=
    Real.rpow_le_rpow_of_nonpos hay hle (by linarith)
  have hy2 : 0 < y ^ 2 := by positivity
  have hm : 0 < min 1 (y ^ 2) := lt_min one_pos hy2
  have h2 : ‖w‖⁻¹ ^ 2 ≤ (min 1 (y ^ 2))⁻¹ * (1 + t ^ 2)⁻¹ := by
    rw [inv_pow, hsq, ← mul_inv]
    apply inv_anti₀ (by positivity)
    have := min_le_left 1 (y ^ 2)
    have := min_le_right 1 (y ^ 2)
    nlinarith [sq_nonneg t]
  calc ‖w‖⁻¹ ^ 2 * ‖w‖ ^ (-2 * σ.re) ≤ ((min 1 (y ^ 2))⁻¹ * (1 + t ^ 2)⁻¹) * |y| ^ (-2 * σ.re) :=
        mul_le_mul h2 h1 (by positivity) (by positivity)
    _ = _ := by ring

theorem phi_line (σ : ℂ) (hσ : 0 < σ.re) (y : ℝ) (hy : y ≠ 0) :
    Continuous (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) ∧
      MeasureTheory.Integrable (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) := by
  have hw : Continuous (fun t : ℝ => ((t : ℂ) + (y : ℂ) * Complex.I)) := by fun_prop
  have hcont : Continuous (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) := by
    unfold GlobalTheory.HeckeTwo.phi
    refine Continuous.mul ((hw.inv₀ fun t => line_ne_zero t y hy).pow 2) ?_
    refine Continuous.cpow (Complex.continuous_ofReal.comp hw.norm) continuous_const ?_
    intro t
    exact Complex.ofReal_mem_slitPlane.2
      (lt_of_lt_of_le (abs_pos.2 hy) (abs_le_norm_line t y))
  refine ⟨hcont, ?_⟩
  refine MeasureTheory.Integrable.mono' (integrable_inv_one_add_sq.const_mul
    (|y| ^ (-2 * σ.re) * (min 1 (y ^ 2))⁻¹)) hcont.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun t => norm_phi_le σ hσ y hy t

end GlobalTheory.HeckeTwo.PhiLine

theorem GlobalTheory.HeckeTwo.phi_line_continuous_integrable : ∀ (σ : ℂ), 0 < σ.re → ∀ (y : ℝ), y ≠ 0 →
    Continuous (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) ∧
      MeasureTheory.Integrable (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) :=
  fun σ hσ y hy => GlobalTheory.HeckeTwo.PhiLine.phi_line σ hσ y hy
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwoExp

variable {F : Type} [Field F] [NumberField F]

theorem phi_zero (w : ℂ) : phi 0 w = w⁻¹ ^ 2 := by
  simp [phi]

theorem hTrans_zero_neg (ν y : ℝ) : hTrans 0 ν (-y) = hTrans 0 (-ν) y := by
  unfold hTrans
  conv_lhs => rw [← MeasureTheory.integral_neg_eq_self]
  congr 1; funext t
  simp only [phi_zero, ofReal_neg]
  congr 1
  · rw [show -(t : ℂ) + -(y : ℂ) * I = -((t : ℂ) + (y : ℂ) * I) by ring, inv_neg, neg_sq]
  · congr 1; ring

theorem emb_nonempty [IsTotallyReal F] : Nonempty (Emb F) := by
  have : Nonempty (F →+* ℂ) := by
    rw [← Fintype.card_pos_iff, NumberField.Embeddings.card]
    exact Module.finrank_pos
  obtain ⟨φ⟩ := this
  exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding⟩

theorem abs_norm_eq_prod [IsTotallyReal F] (ν : F) :
    ((|(Algebra.norm ℚ ν : ℝ)| : ℝ) : ℂ) = ∏ τ : Emb F, ((|τ ν| : ℝ) : ℂ) := by
  have h := prod_emb ν
  have h' : ((Algebra.norm ℚ ν : ℚ) : ℝ) = ∏ τ : Emb F, τ ν := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_prod, h]; push_cast; rfl
  rw [h', Finset.abs_prod, Complex.ofReal_prod]

end GlobalTheory.HeckeTwoExp

namespace GlobalTheory.HeckeTwoExp

variable {F : Type} [Field F] [NumberField F]

def toQ (𝔞 𝔟 : Frac F) : (Σ c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)),
    {ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) // ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1)}) → Quotient (qRel 𝔞 𝔟) :=
  fun s => Quotient.mk _ ⟨(s.2.1.1, s.1.out.1), s.2.1.2.1, s.1.out.2.1, s.2.2⟩

theorem toQ_injective (𝔞 𝔟 : Frac F) : Function.Injective (toQ 𝔞 𝔟) := by
  rintro ⟨c, ν⟩ ⟨c', ν'⟩ h
  obtain ⟨ε, h1, h2⟩ := Quotient.exact h
  dsimp only at h1 h2
  have hc : c = c' := by
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    exact Quotient.sound ⟨ε, h2⟩
  subst hc
  have hne : c.out.1 ≠ 0 := c.out.2.2
  have hε : ((ε : 𝓞 F) : F) = 1 := by
    have h3 : (((ε : 𝓞 F) : F) - 1) * c.out.1 = 0 := by linear_combination -h2
    exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hne)
  have hε' : (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = 1 := by
    have := unit_inv_mul ε; rw [hε, mul_one] at this; exact this
  rw [hε', one_mul] at h1
  have : ν = ν' := Subtype.ext (Subtype.ext h1.symm)
  subst this
  rfl

theorem toQ_surjective [IsTotallyReal F] (𝔞 𝔟 : Frac F) : Function.Surjective (toQ 𝔞 𝔟) := by
  intro q
  induction q using Quotient.inductionOn with
  | h p => ?_
  obtain ⟨⟨ν, b⟩, hν, hb, hpos⟩ := p
  obtain ⟨τ₀⟩ := emb_nonempty (F := F)
  have hνb : ν * b ≠ 0 := by
    intro h0; have := hpos τ₀; rw [h0, map_zero] at this; exact lt_irrefl _ this
  have hb0 : b ≠ 0 := right_ne_zero_of_mul hνb
  have hν0 : ν ≠ 0 := left_ne_zero_of_mul hνb
  set c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) := Quotient.mk _ ⟨b, hb, hb0⟩ with hcdef
  obtain ⟨ε, hε⟩ := Quotient.exact (Quotient.out_eq c : Quotient.mk _ c.out = Quotient.mk _ ⟨b, hb, hb0⟩)
  dsimp only at hε
  have hmem : ((ε : 𝓞 F) : F) * ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) := by
    have := Submodule.smul_mem (𝔞 : FractionalIdeal (𝓞 F)⁰ F).coeToSubmodule (ε : 𝓞 F) hν
    rw [Algebra.smul_def] at this
    exact this
  have hne : ((ε : 𝓞 F) : F) * ν ≠ 0 := by
    refine mul_ne_zero ?_ hν0
    intro h0
    have := unit_inv_mul ε; rw [h0, mul_zero] at this; exact zero_ne_one this
  have hprod : ((ε : 𝓞 F) : F) * ν * c.out.1 = ν * b := by rw [hε]; ring
  refine ⟨⟨c, ⟨⟨((ε : 𝓞 F) : F) * ν, hmem, hne⟩, fun τ => by rw [hprod]; exact hpos τ⟩⟩, ?_⟩
  apply Quotient.sound
  refine ⟨ε, ?_, hε⟩
  show ν = _ * (((ε : 𝓞 F) : F) * ν)
  rw [← mul_assoc, unit_inv_mul, one_mul]

theorem tsum_qClass_eq [IsTotallyReal F] (𝔞 𝔟 : Frac F) (z : Emb F → ℂ) (hS : Summable (qClass 𝔞 𝔟 2 z)) :
    ∑' c, qClass 𝔞 𝔟 2 z c = ∑' c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)),
      ∑' ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F),
        if ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1) then qTerm 𝔞 2 z (ν.1, c.out.1) else 0 := by
  set e := Equiv.ofBijective (toQ 𝔞 𝔟) ⟨toQ_injective 𝔞 𝔟, toQ_surjective 𝔞 𝔟⟩ with he
  have hS' : Summable (qClass 𝔞 𝔟 2 z ∘ e) := e.summable_iff.2 hS
  have h1 : ∑' c, qClass 𝔞 𝔟 2 z c = ∑' p, qClass 𝔞 𝔟 2 z (e p) := (e.tsum_eq _).symm
  have h2 : ∑' p, qClass 𝔞 𝔟 2 z (e p) = ∑' c, ∑' ν, qClass 𝔞 𝔟 2 z (e ⟨c, ν⟩) := hS'.tsum_sigma
  rw [h1, h2]
  refine tsum_congr fun c => ?_
  have h3 := tsum_subtype {ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) | ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1)}
    (fun ν => qTerm 𝔞 2 z (ν.1, c.out.1))
  have h4 : ∀ ν : {ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) // ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1)},
      qClass 𝔞 𝔟 2 z (e ⟨c, ν⟩) = qTerm 𝔞 2 z (ν.1.1, c.out.1) := fun ν => by
    rw [he]; exact qClass_mk 𝔞 𝔟 2 z _
  rw [tsum_congr h4]
  refine h3.trans (tsum_congr fun ν => ?_)
  rw [Set.indicator_apply]
  rfl

end GlobalTheory.HeckeTwoExp

namespace GlobalTheory.HeckeTwoExp

variable {F : Type} [Field F] [NumberField F]

theorem kFac_zero_mul : kFac (F := F) 0 * (-4 * (Real.pi : ℂ) ^ 2) ^ Fintype.card (Emb F) = 1 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : (2 * (Real.pi : ℂ) * I)⁻¹ ^ 2 * (-4 * (Real.pi : ℂ) ^ 2) = 1 := by
    rw [inv_pow, mul_pow, mul_pow, I_sq]
    field_simp
    ring
  unfold kFac
  simp only [mul_zero, cpow_zero, mul_one, Finset.prod_const, Finset.card_univ]
  rw [← mul_pow, h1, one_pow]

theorem dF_pos : 0 < dF F := abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero F))

theorem nrm_ne_zero (𝔞 : Frac F) : nrm 𝔞 ≠ 0 := by
  unfold nrm
  rw [Rat.cast_ne_zero, Ne, FractionalIdeal.absNorm_eq_zero_iff]
  exact 𝔞.ne_zero

end GlobalTheory.HeckeTwoExp
end
end

section

open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge

namespace GlobalTheory.FilPreMem

theorem poly_mem (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ))
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S]
    (a : S → w.valuationSubring) (N : ℕ) (F : Submodule w.valuationSubring (S → Fin N → C))
    (hF : ∀ x ∈ F, GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.unif a x ∈ F) (f : Polynomial (Int0 v)) :
    ∀ y ∈ F, (fun s i => ((f.eval (liftA hv a s) : Int0 v) : C) * y s i) ∈ F := by
  induction f using Polynomial.induction_on with
  | C c =>
    intro y hy
    have := F.smul_mem (⟨(c : C), (hv _).1 c.2⟩ : w.valuationSubring) hy
    convert this using 1
    funext s i
    simp only [Polynomial.eval_C]
    rfl
  | add p q hp hq =>
    intro y hy
    have := F.add_mem (hp y hy) (hq y hy)
    convert this using 1
    funext s i
    simp only [Polynomial.eval_add, Subring.coe_add, Pi.add_apply, add_mul]
  | monomial n c h =>
    intro y hy
    have := hF _ (h y hy)
    convert this using 1
    funext s i
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.unif, Pi.smul_apply, smul_eq_mul, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Subring.coe_mul,
      Subring.coe_pow, pow_succ, liftA]
    ring

theorem filPre_mem_iff : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ)) (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ) (F : Submodule w.valuationSubring (S → Fin N → C)), (∀ x ∈ F, GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.unif a x ∈ F) → ∀ x, x ∈ (Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F}) ↔ evalVec (liftA hv a) N x ∈ F := by
  intro C _ w v hv S _ _ a N F hF x
  let T : Submodule (RS (liftA hv a)) (Fin N → RS (liftA hv a)) :=
    { carrier := {x | evalVec (liftA hv a) N x ∈ F}
      zero_mem' := by
        show evalVec (liftA hv a) N 0 ∈ F
        have : evalVec (liftA hv a) N 0 = 0 := by
          funext s i; simp [evalVec]
        rw [this]; exact F.zero_mem
      add_mem' := by
        intro x y hx hy
        show evalVec (liftA hv a) N (x + y) ∈ F
        rw [evalVec_add]; exact F.add_mem hx hy
      smul_mem' := by
        intro r x hx
        show evalVec (liftA hv a) N (r • x) ∈ F
        induction r using AdjoinRoot.induction_on with
        | ih f =>
          have := poly_mem C w v hv S a N F hF f _ hx
          convert this using 1
          funext s i
          simp [evalVec, ev] }
  constructor
  · intro hx
    have : (Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F}) ≤ T := Submodule.span_le.2 (fun y hy => hy)
    exact this hx
  · intro hx
    exact Submodule.subset_span hx

end GlobalTheory.FilPreMem
end
