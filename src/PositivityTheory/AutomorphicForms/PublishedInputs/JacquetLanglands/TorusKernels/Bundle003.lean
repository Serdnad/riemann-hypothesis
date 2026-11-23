module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Lemma
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
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.HyperbolicKappaLemmas

open UpperTheory.Esk

theorem nsq (z w : ℂ) : ‖z - conj w‖ ^ 2 = (z.re - w.re) ^ 2 + (z.im + w.im) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  ring

theorem pos_den {z w : ℂ} (h : 0 < z.im * w.im) : 0 < ‖z - conj w‖ ^ 2 := by
  rw [nsq]
  nlinarith [sq_nonneg (z.re - w.re), sq_nonneg z.im, sq_nonneg w.im]

theorem kap_of {z w : P} (h : 0 < z.1.im * w.1.im) :
    kap z w = 4 * (z.1.im * w.1.im) / ‖z.1 - conj w.1‖ ^ 2 := by
  unfold kap
  rw [if_pos h]

theorem kap_of_not {z w : P} (h : ¬ 0 < z.1.im * w.1.im) : kap z w = 0 := by
  unfold kap
  rw [if_neg h]

theorem kap_nonneg (z w : P) : 0 ≤ kap z w := by
  unfold kap
  split_ifs with h
  · exact div_nonneg (by linarith) (sq_nonneg _)
  · exact le_rfl

theorem key {z w u : ℂ} (h1 : 0 < z.im * w.im) (h2 : 0 < w.im * u.im) :
    w.im ^ 2 * ‖z - conj u‖ ^ 2 ≤ ‖z - conj w‖ ^ 2 * ‖w - conj u‖ ^ 2 := by
  have h13 : 0 < z.im * u.im := by
    by_contra hc
    have hc := not_lt.mp hc
    nlinarith [mul_pos h1 h2, mul_nonneg (neg_nonneg.mpr hc) (sq_nonneg w.im)]
  have hp : 0 ≤ z.im ^ 2 + 2 * z.im * w.im := by nlinarith [sq_nonneg z.im]
  have hq : 0 ≤ u.im ^ 2 + 2 * w.im * u.im := by nlinarith [sq_nonneg u.im]
  rw [nsq, nsq, nsq]
  nlinarith [sq_nonneg ((z.re - w.re) * (w.re - u.re) - w.im ^ 2),
    mul_nonneg (sq_nonneg (z.re - w.re)) hq, mul_nonneg (sq_nonneg (w.re - u.re)) hp,
    mul_nonneg (sq_nonneg w.im) h1.le, mul_nonneg (sq_nonneg w.im) h2.le,
    mul_nonneg (sq_nonneg w.im) h13.le, mul_nonneg h13.le h1.le, mul_nonneg h13.le h2.le,
    sq_nonneg (z.im * u.im)]

theorem p1 (z w : P) : 0 ≤ kap z w ∧ kap z w ≤ 1 ∧ kap z w = kap w z := by
  refine ⟨kap_nonneg z w, ?_, ?_⟩
  · by_cases h : 0 < z.1.im * w.1.im
    · rw [kap_of h, div_le_iff₀ (pos_den h), nsq]
      nlinarith [sq_nonneg (z.1.re - w.1.re), sq_nonneg (z.1.im - w.1.im)]
    · rw [kap_of_not h]
      norm_num
  · have e2 : ‖w.1 - conj z.1‖ ^ 2 = ‖z.1 - conj w.1‖ ^ 2 := by
      rw [nsq, nsq]
      ring
    unfold kap
    rw [mul_comm w.1.im z.1.im, e2]

theorem p2 (z : P) : kap z z = 1 := by
  have h : 0 < z.1.im * z.1.im := mul_self_pos.mpr z.2
  rw [kap_of h, div_eq_one_iff_eq (pos_den h).ne', nsq]
  ring

theorem p3 (z w u : P) : kap z w * kap w u ≤ 4 * kap z u := by
  by_cases h1 : 0 < z.1.im * w.1.im
  · by_cases h2 : 0 < w.1.im * u.1.im
    · have h13 : 0 < z.1.im * u.1.im := by
        by_contra hc
        have hc := not_lt.mp hc
        nlinarith [mul_pos h1 h2, mul_nonneg (neg_nonneg.mpr hc) (sq_nonneg w.1.im)]
      have hA := pos_den h1
      have hB := pos_den h2
      have hC := pos_den h13
      have hk := mul_le_mul_of_nonneg_left (key h1 h2) h13.le
      rw [kap_of h1, kap_of h2, kap_of h13, div_mul_div_comm, mul_div_assoc', le_div_iff₀ hC,
        div_mul_eq_mul_div, div_le_iff₀ (mul_pos hA hB)]
      nlinarith [hk]
    · rw [kap_of_not h2, mul_zero]
      exact mul_nonneg (by norm_num) (kap_nonneg z u)
  · rw [kap_of_not h1, zero_mul]
    exact mul_nonneg (by norm_num) (kap_nonneg z u)

theorem p4 (z w : P) : kap z w * |w.1.im| ≤ 4 * |z.1.im| := by
  by_cases h : 0 < z.1.im * w.1.im
  · rw [kap_of h, div_mul_eq_mul_div, div_le_iff₀ (pos_den h), nsq]
    rcases lt_or_gt_of_ne w.2 with hw | hw
    · have hz : z.1.im < 0 := by nlinarith [h, hw]
      rw [abs_of_neg hw, abs_of_neg hz]
      nlinarith [mul_nonneg (neg_nonneg.mpr hz.le) (sq_nonneg (z.1.re - w.1.re)),
        mul_nonneg (neg_nonneg.mpr hz.le) (sq_nonneg z.1.im),
        mul_nonneg (sq_nonneg z.1.im) (neg_nonneg.mpr hw.le)]
    · have hz : 0 < z.1.im := by nlinarith [h, hw]
      rw [abs_of_pos hw, abs_of_pos hz]
      nlinarith [mul_nonneg hz.le (sq_nonneg (z.1.re - w.1.re)), mul_nonneg hz.le (sq_nonneg z.1.im),
        mul_nonneg (sq_nonneg z.1.im) hw.le]
  · rw [kap_of_not h, zero_mul]
    positivity

theorem p5 : Continuous (fun p : P × P => kap p.1 p.2) := by
  have hv1 : Continuous (fun p : P × P => p.1.1) := continuous_subtype_val.comp continuous_fst
  have hv2 : Continuous (fun p : P × P => p.2.1) := continuous_subtype_val.comp continuous_snd
  have hc : Continuous (fun p : P × P => p.1.1.im * p.2.1.im) :=
    (Complex.continuous_im.comp hv1).mul (Complex.continuous_im.comp hv2)
  have hd : Continuous (fun p : P × P => ‖p.1.1 - conj p.2.1‖ ^ 2) :=
    ((hv1.sub (Complex.continuous_conj.comp hv2)).norm).pow 2
  have hopen : IsOpen {p : P × P | 0 < p.1.1.im * p.2.1.im} := isOpen_lt continuous_const hc
  have hclosed : IsClosed {p : P × P | 0 < p.1.1.im * p.2.1.im} := by
    have e : {p : P × P | 0 < p.1.1.im * p.2.1.im} = {p : P × P | 0 ≤ p.1.1.im * p.2.1.im} := by
      ext p
      simp only [Set.mem_setOf_eq]
      exact ⟨fun h => le_of_lt h, fun h => lt_of_le_of_ne h (Ne.symm (mul_ne_zero p.1.2 p.2.2))⟩
    rw [e]
    exact isClosed_le continuous_const hc
  have hfr : frontier {p : P × P | 0 < p.1.1.im * p.2.1.im} = ∅ := by
    rw [frontier, hclosed.closure_eq, hopen.interior_eq, Set.sdiff_self]
  show Continuous (fun p : P × P => if 0 < p.1.1.im * p.2.1.im then
    4 * (p.1.1.im * p.2.1.im) / ‖p.1.1 - conj p.2.1‖ ^ 2 else 0)
  apply continuous_if
  · intro a ha
    simp [hfr] at ha
  · rw [hclosed.closure_eq]
    exact ((continuous_const.mul hc).continuousOn).div hd.continuousOn
      (fun p hp => (pos_den (z := p.1.1) (w := p.2.1) hp).ne')
  · exact continuousOn_const

theorem p6 (z : P) : ∃ g : GL (Fin 2) ℝ, g 1 0 = 0 ∧ g 1 1 = 1 ∧ g • iP = z := by
  have hdet : (!![z.1.im, z.1.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    simpa using z.2
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, rfl, rfl, Subtype.ext ?_⟩
  rw [coe_smul]
  show num (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) Complex.I /
    den (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) Complex.I = z.1
  have h00 : (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) 0 0 = z.1.im := rfl
  have h01 : (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) 0 1 = z.1.re := rfl
  have h10 : (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) 1 0 = 0 := rfl
  have h11 : (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) 1 1 = 1 := rfl
  rw [num, den, h00, h01, h10, h11]
  apply Complex.ext <;> simp

end UpperTheory.Esk.HyperbolicKappaLemmas

namespace UpperTheory.Esk

theorem hyperbolic_kappa_properties_proof : B1c := by
  unfold B1c
  exact ⟨HyperbolicKappaLemmas.p1, HyperbolicKappaLemmas.p2, HyperbolicKappaLemmas.p3, HyperbolicKappaLemmas.p4, HyperbolicKappaLemmas.p5, HyperbolicKappaLemmas.p6⟩

end UpperTheory.Esk
end
end

section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UpperTheory.Esk.AnnihilatorQuotientResidues

variable {G Y : Type} [Group G] [MeasurableSpace Y] [MulAction G Y] {μ : Measure Y}

def actEquiv (hP : Pres G μ) (g : G) : Y ≃ᵐ Y where
  toEquiv := MulAction.toPerm g
  measurable_toFun := (hP g).measurable
  measurable_invFun := (hP g⁻¹).measurable

lemma embed (hP : Pres G μ) (g : G) : MeasurableEmbedding (fun y : Y => g • y) :=
  (actEquiv hP g).measurableEmbedding

lemma enorm_cut {b : Y → ℝ} (hb : IsCut G b) (y : Y) (x : ℂ) :
    ‖b y • x‖ₑ = ENNReal.ofReal (b y) * ‖x‖ₑ := by
  rw [enorm_smul, Real.enorm_eq_ofReal (hb.nonneg y)]

lemma lint_split [Countable G] (hP : Pres G μ) {b b' : Y → ℝ} (hb : IsCut G b) (hb' : IsCut G b')
    (u : Y → ℝ≥0∞) (hu : Measurable u) :
    ∫⁻ y, ENNReal.ofReal (b y) * u y ∂μ
      = ∑' g : G, ∫⁻ y, ENNReal.ofReal (b' (g • y)) * (ENNReal.ofReal (b y) * u y) ∂μ := by
  rw [← lintegral_tsum]
  · congr 1
    funext y
    rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun g => hb'.nonneg _)
      (hb'.sum y).summable, (hb'.sum y).tsum_eq, ENNReal.ofReal_one, one_mul]
  · intro g
    exact ((ENNReal.measurable_ofReal.comp (hb'.meas.comp (hP g).measurable)).mul
      ((ENNReal.measurable_ofReal.comp hb.meas).mul hu)).aemeasurable

lemma lint_term (hP : Pres G μ) {b b' : Y → ℝ} (u : Y → ℝ≥0∞)
    (hinv : ∀ (g : G) y, u (g • y) = u y) (g : G) :
    ∫⁻ y, ENNReal.ofReal (b' (g • y)) * (ENNReal.ofReal (b y) * u y) ∂μ
      = ∫⁻ y, ENNReal.ofReal (b (g⁻¹ • y)) * (ENNReal.ofReal (b' y) * u y) ∂μ := by
  have h := (hP g).lintegral_comp_emb (embed hP g)
    (fun z => ENNReal.ofReal (b (g⁻¹ • z)) * (ENNReal.ofReal (b' z) * u z))
  rw [← h]
  congr 1
  funext y
  simp only [inv_smul_smul, hinv, mul_left_comm]

lemma lint_eq [Countable G] (hP : Pres G μ) {b b' : Y → ℝ} (hb : IsCut G b) (hb' : IsCut G b')
    (u : Y → ℝ≥0∞) (hu : Measurable u) (hinv : ∀ (g : G) y, u (g • y) = u y) :
    ∫⁻ y, ENNReal.ofReal (b y) * u y ∂μ = ∫⁻ y, ENNReal.ofReal (b' y) * u y ∂μ := by
  rw [lint_split hP hb hb' u hu, lint_split hP hb' hb u hu]
  calc _ = ∑' g : G, ∫⁻ y, ENNReal.ofReal (b (g⁻¹ • y)) * (ENNReal.ofReal (b' y) * u y) ∂μ :=
        tsum_congr (lint_term hP u hinv)
    _ = _ := (Equiv.inv G).tsum_eq
        (fun g => ∫⁻ y, ENNReal.ofReal (b (g • y)) * (ENNReal.ofReal (b' y) * u y) ∂μ)

lemma integrable_swap [Countable G] (hP : Pres G μ) {b b' : Y → ℝ} (hb : IsCut G b) (hb' : IsCut G b')
    (u : Y → ℂ) (hu : Measurable u) (hinv : ∀ (g : G) y, u (g • y) = u y)
    (hi : Integrable (fun y => b y • u y) μ) : Integrable (fun y => b' y • u y) μ := by
  refine ⟨(hb'.meas.smul hu).aestronglyMeasurable, ?_⟩
  have h := hi.hasFiniteIntegral
  have e := lint_eq hP hb hb' (fun y => ‖u y‖ₑ) hu.enorm (fun g y => by simp only [hinv])
  simp only [HasFiniteIntegral, enorm_cut hb, enorm_cut hb'] at h ⊢
  rwa [← e]

lemma int_split [Countable G] (hP : Pres G μ) {b b' : Y → ℝ} (hb : IsCut G b) (hb' : IsCut G b')
    (u : Y → ℂ) (hu : Measurable u) (hi : Integrable (fun y => b y • u y) μ) :
    ∫ y, b y • u y ∂μ = ∑' g : G, ∫ y, b' (g • y) • (b y • u y) ∂μ := by
  rw [← integral_tsum]
  · congr 1
    funext y
    rw [(hb'.sum y).summable.tsum_smul_const, (hb'.sum y).tsum_eq, one_smul]
  · intro g
    exact ((hb'.meas.comp (hP g).measurable).smul (hb.meas.smul hu)).aestronglyMeasurable
  · have h := hi.hasFiniteIntegral
    have e := lint_split hP hb hb' (fun y => ‖u y‖ₑ) hu.enorm
    simp only [HasFiniteIntegral, enorm_cut hb, enorm_cut hb'] at h e ⊢
    rw [← e]
    exact h.ne

lemma int_term (hP : Pres G μ) {b b' : Y → ℝ} (u : Y → ℂ)
    (hinv : ∀ (g : G) y, u (g • y) = u y) (g : G) :
    ∫ y, b' (g • y) • (b y • u y) ∂μ = ∫ y, b (g⁻¹ • y) • (b' y • u y) ∂μ := by
  have h := (hP g).integral_comp (embed hP g) (fun z => b (g⁻¹ • z) • (b' z • u z))
  rw [← h]
  congr 1
  funext y
  rw [inv_smul_smul, hinv, smul_comm]

lemma int_eq [Countable G] (hP : Pres G μ) {b b' : Y → ℝ} (hb : IsCut G b) (hb' : IsCut G b')
    (u : Y → ℂ) (hu : Measurable u) (hinv : ∀ (g : G) y, u (g • y) = u y)
    (hi : Integrable (fun y => b y • u y) μ) (hi' : Integrable (fun y => b' y • u y) μ) :
    ∫ y, b y • u y ∂μ = ∫ y, b' y • u y ∂μ := by
  rw [int_split hP hb hb' u hu hi, int_split hP hb' hb u hu hi']
  calc _ = ∑' g : G, ∫ y, b (g⁻¹ • y) • (b' y • u y) ∂μ := tsum_congr (int_term hP u hinv)
    _ = _ := (Equiv.inv G).tsum_eq (fun g => ∫ y, b (g • y) • (b' y • u y) ∂μ)

end UpperTheory.Esk.AnnihilatorQuotientResidues

theorem UpperTheory.Esk.action_integral_swap_proof : UpperTheory.Esk.C1 := by
  intro G Y _ _ _ _ μ hP b b' hb hb'
  refine ⟨fun u hu hinv => UpperTheory.Esk.AnnihilatorQuotientResidues.lint_eq hP hb hb' u hu hinv, fun u hu hinv hi => ?_⟩
  have hi' := UpperTheory.Esk.AnnihilatorQuotientResidues.integrable_swap hP hb hb' u hu hinv hi
  exact ⟨hi', UpperTheory.Esk.AnnihilatorQuotientResidues.int_eq hP hb hb' u hu hinv hi hi'⟩
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.RadialIntegralLemmas
open UpperTheory.Esk

def F (k : ℕ) (g : GL (Fin 2) ℝ) (z : P) : ℂ := q1 k z (g • z) * j1 k g z

def U (k : ℕ) (g : GL (Fin 2) ℝ) (z : P) : ℂ := if 0 < z.1.im then F k g z else 0

def eta (a b : ℝ) : ℂ := ((a : ℂ) - b * Complex.I) / (Real.sqrt (a ^ 2 + b ^ 2) : ℂ)

end UpperTheory.Esk.RadialIntegralLemmas
end
end

section

noncomputable section

open MeasureTheory

namespace UpperTheory.Esk.CountingMeasureInvariance

variable {G Ω X : Type} [Group G] [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω] [Countable Ω]
  [MeasurableSpace X] [MulAction G Ω] [MulAction G X]

theorem meas_of_left {f : Ω × X → ℝ} (hf : ∀ ω, Measurable fun x => f (ω, x)) : Measurable f := by
  intro s hs
  have : f ⁻¹' s = ⋃ ω : Ω, ({ω} : Set Ω) ×ˢ ((fun x => f (ω, x)) ⁻¹' s) := by
    ext ⟨ω, x⟩; simp
  rw [this]
  exact MeasurableSet.iUnion fun ω => (MeasurableSet.of_discrete (s := {ω})).prod (hf ω hs)

omit [Countable Ω] in
theorem count_pres (g : G) :
    MeasurePreserving (fun ω : Ω => g • ω) Measure.count Measure.count := by
  have hm : ∀ h : G, Measurable (fun ω : Ω => h • ω) := fun h => Measurable.of_discrete
  refine ⟨hm g, le_antisymm ((MulAction.injective g).map_count_le (hm g)) ?_⟩
  calc (Measure.count : Measure Ω)
      = (Measure.count.map (fun ω : Ω => g⁻¹ • ω)).map (fun ω => g • ω) := by
        rw [Measure.map_map (hm g) (hm g⁻¹)]
        simp [Function.comp_def]
    _ ≤ Measure.count.map (fun ω : Ω => g • ω) :=
        Measure.map_mono ((MulAction.injective g⁻¹).map_count_le (hm _)) (hm g)

theorem pres_prod (μ : Measure X) [SigmaFinite μ] (hμ : Pres G μ) :
    Pres G ((Measure.count : Measure Ω).prod μ) := fun g =>
  (count_pres g).prod (hμ g)


open Classical in
def cut (R : Set Ω) (β : Ω → X → ℝ) (p : Ω × X) : ℝ := by
  classical
  exact if p.1 ∈ R then β p.1 p.2 else 0

theorem cut_isCut (R : Set Ω) (hR : ∀ ω, ∃! r, r ∈ R ∧ r ∈ MulAction.orbit G ω) (β : Ω → X → ℝ)
    (hβ : ∀ r ∈ R, IsCut (MulAction.stabilizer G r) (β r)) : IsCut G (cut R β) := by
  refine ⟨?_, ?_, ?_⟩
  · refine meas_of_left fun ω => ?_
    by_cases h : ω ∈ R
    · simpa [cut, h] using (hβ ω h).meas
    · simp [cut, h]
  · rintro ⟨ω, x⟩
    unfold cut
    split_ifs with h
    · exact (hβ _ h).nonneg x
    · exact le_rfl
  · rintro ⟨ω, x⟩
    obtain ⟨r, ⟨hrR, g₀, hg₀'⟩, hu⟩ := hR ω
    have hg₀ : g₀ • ω = r := hg₀'
    have key : ∀ g : G, g • ω ∈ R → g • ω = r := fun g hg => hu _ ⟨hg, MulAction.mem_orbit ω g⟩
    let e : MulAction.stabilizer G r → G := fun s => (s : G) * g₀
    have he : Function.Injective e := fun s t h => Subtype.ext (mul_right_cancel h)
    rw [← he.hasSum_iff]
    · convert (hβ r hrR).sum (g₀ • x) using 1
      funext s
      have hs : (s : G) • r = r := s.2
      have h2 : ((s : G) * g₀) • ω = r := by rw [mul_smul, hg₀, hs]
      simp only [Function.comp_apply, e, cut, Prod.smul_mk, h2, mul_smul, Subgroup.smul_def]
      split_ifs with hc
      · rfl
      · exact absurd (h2.symm ▸ hrR) hc
    · intro g hg
      simp only [cut, Prod.smul_mk]
      rw [ite_eq_right]
      intro hgR
      apply hg
      refine ⟨⟨g * g₀⁻¹, ?_⟩, ?_⟩
      · rw [MulAction.mem_stabilizer_iff, mul_smul, ← hg₀, inv_smul_smul, key g hgR, hg₀]
      · simp [e]

end UpperTheory.Esk.CountingMeasureInvariance

open UpperTheory.Esk.CountingMeasureInvariance in
theorem UpperTheory.Esk.counting_measure_invariance_proof : UpperTheory.Esk.C1 → UpperTheory.Esk.C4 := by
  intro hC1 G Ω X _ _ _ _ _ _ _ _ μ _ hμ b hb u hu hinv hint R hR β hβ
  have hP : Pres G ((Measure.count : Measure Ω).prod μ) := pres_prod μ hμ
  have hb' := cut_isCut R hR β hβ
  obtain ⟨hI', hE⟩ := (hC1 G (Ω × X) ((Measure.count : Measure Ω).prod μ) hP b (cut R β) hb hb').2
    u hu hinv hint
  have hsec : ∀ ω, Integrable (fun x => cut R β (ω, x) • u (ω, x)) μ := by
    have := hI'.prod_right_ae
    rwa [Measure.ae_count_iff] at this
  have hF : Integrable (fun ω => ∫ x, cut R β (ω, x) • u (ω, x) ∂μ) Measure.count :=
    hI'.integral_prod_left
  have hsum : HasSum (fun ω => ∫ x, cut R β (ω, x) • u (ω, x) ∂μ)
      (∫ y, b y • u y ∂((Measure.count : Measure Ω).prod μ)) := by
    rw [hE, integral_prod _ hI', integral_countable hF]
    simp only [count_real_singleton, one_smul]
    exact (integrable_count_iff.mp hF).of_norm.hasSum
  refine ⟨fun r hr => by simpa [cut, hr] using hsec r, ?_⟩
  have hsupp : Function.support (fun ω => ∫ x, cut R β (ω, x) • u (ω, x) ∂μ) ⊆ R := by
    intro ω hω
    by_contra h
    apply hω
    simp [cut, h]
  rw [← hasSum_subtype_iff_of_support_subset hsupp] at hsum
  convert hsum using 1
  funext r
  simp [cut, r.2]
end
end
