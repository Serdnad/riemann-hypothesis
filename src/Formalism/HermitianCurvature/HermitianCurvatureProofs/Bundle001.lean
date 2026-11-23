module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Tactic.ToDual
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
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
public import Mathlib.MeasureTheory.Function.L2Space
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

section

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.TVCrdAlg

variable {R : Type*} [Ring R]

def cont (D e : ℕ → R) (a : ℕ) : ℕ → R
  | 0 => 1
  | 1 => D a
  | n + 2 => D (a + n + 1) * cont D e a (n + 1) - e (a + n + 1) * cont D e a n

theorem cont_zero (D e : ℕ → R) (a : ℕ) : cont D e a 0 = 1 := rfl

theorem cont_one (D e : ℕ → R) (a : ℕ) : cont D e a 1 = D a := rfl

theorem cont_two (D e : ℕ → R) (a n : ℕ) :
    cont D e a (n + 2) = D (a + n + 1) * cont D e a (n + 1) - e (a + n + 1) * cont D e a n := rfl

theorem cont_top (D e : ℕ → R) (hDe : ∀ i j, i + 1 ≤ j → D j * e i = e i * D j)
    (hee : ∀ i j, e i * e j = e j * e i) :
    ∀ n a, cont D e a (n + 2) = cont D e (a + 1) (n + 1) * D a - e (a + 1) * cont D e (a + 2) n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
    intro a
    rfl
  | one =>
    intro a
    change D (a + 2) * (D (a + 1) * D a - e (a + 1) * 1) - e (a + 2) * D a =
      (D (a + 2) * D (a + 1) - e (a + 2) * 1) * D a - e (a + 1) * D (a + 2)
    have hc := hDe (a + 1) (a + 2) (by omega)
    simp only [mul_one, mul_sub, sub_mul, ← mul_assoc, hc]
    abel
  | more n ih0 ih1 =>
    intro a
    have eA : cont D e a (n + 2 + 2) =
        D (a + n + 3) * cont D e a (n + 1 + 2) - e (a + n + 3) * cont D e a (n + 2) := rfl
    have eB : cont D e (a + 1) (n + 2 + 1) =
        D (a + n + 3) * cont D e (a + 1) (n + 2) - e (a + n + 3) * cont D e (a + 1) (n + 1) := by
      rw [show n + 2 + 1 = (n + 1) + 2 by omega, cont_two, show a + 1 + (n + 1) + 1 = a + n + 3 by omega]
    have eC : cont D e (a + 2) (n + 2) =
        D (a + n + 3) * cont D e (a + 2) (n + 1) - e (a + n + 3) * cont D e (a + 2) n := by
      rw [cont_two, show a + 2 + n + 1 = a + n + 3 by omega]
    rw [eA, eB, eC, ih1 a, ih0 a]
    have hc1 := hDe (a + 1) (a + n + 3) (by omega)
    have hc2 := hee (a + n + 3) (a + 1)
    simp only [mul_sub, sub_mul, ← mul_assoc, hc1, hc2]
    abel

def topK (Dt e : ℕ → R) (r : ℕ) : ℕ → R × R
  | 0 => (1, 0)
  | m + 1 => ((topK Dt e r m).1 * Dt m - e (r - m) * (topK Dt e r m).2, (topK Dt e r m).1)

theorem topK_eq (D e : ℕ → R) (hDe : ∀ i j, i + 1 ≤ j → D j * e i = e i * D j)
    (hee : ∀ i j, e i * e j = e j * e i) (r : ℕ) (Dt : ℕ → R) (hDt : ∀ m < r, Dt m = D (r - m - 1)) :
    ∀ m, m ≤ r → (topK Dt e r m).1 = cont D e (r - m) m ∧
      (topK Dt e r m).2 = if m = 0 then 0 else cont D e (r - m + 1) (m - 1) := by
  intro m
  induction m with
  | zero => simp [topK, cont_zero]
  | succ m ih =>
    intro hm
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    simp only [topK]
    refine ⟨?_, ?_⟩
    · rw [ih1, ih2, hDt m (by omega)]
      rcases m with _ | m
      · simp only [ite_true, mul_zero, sub_zero, cont_zero, one_mul, Nat.sub_zero]
        rfl
      · obtain ⟨a, rfl⟩ : ∃ a, r = a + m + 2 := ⟨r - m - 2, by omega⟩
        rw [ite_eq_right (by omega), show a + m + 2 - (m + 1) = a + 1 by omega,
          show a + 1 - 1 = a by omega, show a + 1 + 1 = a + 2 by omega,
          show a + m + 2 - (m + 1 + 1) = a by omega, show m + 1 - 1 = m by omega, cont_top D e hDe hee m a]
    · rw [ih1, ite_eq_right (by omega), show m + 1 - 1 = m by omega, show r - (m + 1) + 1 = r - m by omega]

theorem topK_conj (G : R) (Dw Dy e : ℕ → R) (r : ℕ) (hG : ∀ m < r, G * Dw m = Dy m * G)
    (hGe : ∀ j, G * e j = e j * G) :
    ∀ m, m ≤ r → G * (topK Dw e r m).1 = (topK Dy e r m).1 * G ∧
      G * (topK Dw e r m).2 = (topK Dy e r m).2 * G := by
  intro m
  induction m with
  | zero => simp [topK]
  | succ m ih =>
    intro hm
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    simp only [topK]
    refine ⟨?_, ih1⟩
    rw [mul_sub, ← mul_assoc, ih1, mul_assoc, hG m (by omega), ← mul_assoc G (e (r - m)), hGe,
      mul_assoc (e (r - m)) G, ih2, sub_mul, mul_assoc, mul_assoc]

def botA (D Cb Cbi : ℕ → R) (r : ℕ) : ℕ → R × R
  | 0 => (1, 0)
  | i + 1 => if i < r then
      (D i * (botA D Cb Cbi r i).1 - Cb i * (botA D Cb Cbi r i).2, Cbi i * (botA D Cb Cbi r i).1)
      else botA D Cb Cbi r i

theorem botA_eq (D Cb Cbi : ℕ → R) (r : ℕ) :
    ∀ i, i ≤ r → (botA D Cb Cbi r i).1 = cont D (fun j => Cb j * Cbi (j - 1)) 0 i ∧
      (botA D Cb Cbi r i).2 =
        if i = 0 then 0 else Cbi (i - 1) * cont D (fun j => Cb j * Cbi (j - 1)) 0 (i - 1) := by
  intro i
  induction i with
  | zero => simp [botA, cont_zero]
  | succ i ih =>
    intro hi
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    simp only [botA, ite_eq_left (show i < r by omega)]
    refine ⟨?_, ?_⟩
    · rw [ih1, ih2]
      rcases i with _ | i
      · simp only [ite_true, mul_zero, sub_zero, cont_zero, mul_one]
        rfl
      · rw [ite_eq_right (by omega), cont_two, show 0 + i + 1 = i + 1 by omega, show i + 1 - 1 = i by omega,
          mul_assoc]
    · rw [ih1, ite_eq_right (by omega), show i + 1 - 1 = i by omega]

end Formalism.FourierDecayAlt.P.CutMP.TVCrdAlg
end
end

section

open MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

section LogBump

def bumpR : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

def psiL (n : ℕ) (c : ℂ) : ℝ := if c = 0 then 0 else bumpR (Real.log ‖c‖ / ((n : ℝ) + 1))

theorem psiL_le_one (n : ℕ) (c : ℂ) : |psiL n c| ≤ 1 := by
  unfold psiL
  split_ifs
  · simp
  · rw [abs_of_nonneg bumpR.nonneg]
    exact bumpR.le_one

theorem psiL_eq_near (n : ℕ) (c : ℂ) (hc : c ≠ 0) :
    psiL n =ᶠ[𝓝 c] fun w => bumpR (Real.log ‖w‖ / ((n : ℝ) + 1)) := by
  filter_upwards [isOpen_ne.mem_nhds hc] with w hw
  simp [psiL, hw]

theorem psiL_zero_of (n : ℕ) (w : ℂ) (hw : 2 * ((n : ℝ) + 1) ≤ |Real.log ‖w‖|) : psiL n w = 0 := by
  unfold psiL
  split_ifs with h
  · rfl
  · apply bumpR.zero_of_le_dist
    have hpos : (0:ℝ) < (n:ℝ) + 1 := by positivity
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hpos, le_div_iff₀ hpos]
    exact hw

theorem psiL_one_near (n : ℕ) (c : ℂ) (hc : c ≠ 0) (h : |Real.log ‖c‖| < (n : ℝ) + 1) :
    psiL n =ᶠ[𝓝 c] fun _ => 1 := by
  have hcont : ContinuousAt (fun w : ℂ => |Real.log ‖w‖|) c :=
    ((Real.continuousAt_log (norm_ne_zero_iff.2 hc)).comp continuous_norm.continuousAt).abs
  have h1 : ∀ᶠ w in 𝓝 c, |Real.log ‖w‖| < (n:ℝ) + 1 := hcont.eventually_lt continuousAt_const h
  filter_upwards [isOpen_ne.mem_nhds hc, h1] with w hw hw1
  simp only [psiL, if_neg hw]
  apply bumpR.one_of_mem_closedBall
  have hpos : (0:ℝ) < (n:ℝ) + 1 := by positivity
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  show |Real.log ‖w‖| ≤ 1 * ((n:ℝ) + 1)
  linarith

theorem psiL_zero_near0 (n : ℕ) : psiL n =ᶠ[𝓝 0] fun _ => 0 := by
  have hε : (0:ℝ) < Real.exp (-(2 * ((n:ℝ) + 1))) := Real.exp_pos _
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) hε] with w hw
  by_cases h0 : w = 0
  · simp [psiL, h0]
  · apply psiL_zero_of
    rw [Metric.mem_ball, dist_zero_right] at hw
    have hlog : Real.log ‖w‖ < -(2 * ((n:ℝ) + 1)) := by
      rw [Real.log_lt_iff_lt_exp (norm_pos_iff.2 h0)]
      exact hw
    rw [abs_of_neg (by linarith)]
    linarith

theorem psiL_contDiffAt (n : ℕ) (c : ℂ) : ContDiffAt ℝ ∞ (psiL n) c := by
  by_cases hc : c = 0
  · subst hc
    exact (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq (psiL_zero_near0 n)
  · refine ContDiffAt.congr_of_eventuallyEq ?_ (psiL_eq_near n c hc)
    have h1 : ContDiffAt ℝ ∞ (fun w : ℂ => ‖w‖) c := contDiffAt_norm ℝ hc
    have h2 : ContDiffAt ℝ ∞ (fun w : ℂ => Real.log ‖w‖) c :=
      (Real.contDiffAt_log.2 (norm_ne_zero_iff.2 hc)).comp c h1
    have h3 : ContDiffAt ℝ ∞ (fun w : ℂ => Real.log ‖w‖ / ((n:ℝ) + 1)) c := h2.div_const _
    exact bumpR.contDiff.contDiffAt.comp c h3

theorem psiL_contDiff (n : ℕ) : ContDiff ℝ ∞ (psiL n) := contDiff_iff_contDiffAt.2 (psiL_contDiffAt n)

theorem tsupport_psiL (n : ℕ) : tsupport (psiL n) ⊆
    {c : ℂ | Real.exp (-(2 * ((n : ℝ) + 1))) ≤ ‖c‖ ∧ ‖c‖ ≤ Real.exp (2 * ((n : ℝ) + 1))} := by
  refine closure_minimal (fun c hc => ?_)
    ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
  have hc' : psiL n c ≠ 0 := hc
  have h0 : c ≠ 0 := by
    rintro rfl
    exact hc' (by simp [psiL])
  have hlog : |Real.log ‖c‖| < 2 * ((n:ℝ) + 1) := by
    by_contra hle
    push_neg at hle
    exact hc' (psiL_zero_of n c hle)
  have hpos := norm_pos_iff.2 h0
  rw [abs_lt] at hlog
  constructor
  · rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.2 (by linarith [hlog.1])
  · rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.2 (by linarith [hlog.2])

theorem psiL_hasCompactSupport (n : ℕ) : HasCompactSupport (psiL n) := by
  refine (isCompact_closedBall (0:ℂ) (Real.exp (2 * ((n:ℝ) + 1)))).of_isClosed_subset (isClosed_tsupport _) ?_
  intro c hc
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (tsupport_psiL n hc).2

theorem zero_notMem_tsupport_psiL (n : ℕ) : (0 : ℂ) ∉ tsupport (psiL n) := by
  intro h
  have h1 := (tsupport_psiL n h).1
  rw [norm_zero] at h1
  exact absurd h1 (not_le.2 (Real.exp_pos _))

theorem exists_deriv_bump_bound : ∃ C : ℝ, ∀ t, ‖deriv bumpR t‖ ≤ C := by
  have hc : Continuous (deriv bumpR) := (bumpR.contDiff (n := 1)).continuous_deriv le_rfl
  exact hc.bounded_above_of_compact_support bumpR.hasCompactSupport.deriv

theorem norm_mul_fderiv_psiL_le {C : ℝ} (hC : ∀ t, ‖deriv bumpR t‖ ≤ C) (n : ℕ) (c : ℂ) (hc : c ≠ 0) :
    ‖c‖ * ‖fderiv ℝ (psiL n) c‖ ≤ C := by
  have hpos : 0 < ‖c‖ := norm_pos_iff.2 hc
  have hn1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have hnd : DifferentiableAt ℝ (fun w : ℂ => ‖w‖) c := (contDiffAt_norm ℝ hc (n := 1)).differentiableAt one_ne_zero
  have hN : ‖fderiv ℝ (fun w : ℂ => ‖w‖) c‖ ≤ 1 := by
    simpa using norm_fderiv_le_of_lipschitz ℝ (x₀ := c) lipschitzWith_one_norm
  have hl : HasFDerivAt (fun w : ℂ => Real.log ‖w‖) ((‖c‖)⁻¹ • fderiv ℝ (fun w : ℂ => ‖w‖) c) c :=
    (Real.hasDerivAt_log hpos.ne').comp_hasFDerivAt c hnd.hasFDerivAt
  have hφ : HasFDerivAt (fun w : ℂ => Real.log ‖w‖ / ((n:ℝ) + 1))
      ((((n:ℝ) + 1)⁻¹) • ((‖c‖)⁻¹ • fderiv ℝ (fun w : ℂ => ‖w‖) c)) c := by
    have h2 := hl.mul_const (((n:ℝ) + 1)⁻¹)
    simpa only [div_eq_mul_inv] using h2
  have hb : HasDerivAt (⇑bumpR) (deriv bumpR (Real.log ‖c‖ / ((n:ℝ) + 1))) (Real.log ‖c‖ / ((n:ℝ) + 1)) :=
    ((bumpR.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
  have hcomp := hb.comp_hasFDerivAt c hφ
  have hf : fderiv ℝ (psiL n) c = deriv bumpR (Real.log ‖c‖ / ((n:ℝ) + 1)) •
      ((((n:ℝ) + 1)⁻¹) • ((‖c‖)⁻¹ • fderiv ℝ (fun w : ℂ => ‖w‖) c)) :=
    (psiL_eq_near n c hc).fderiv_eq.trans hcomp.fderiv
  have e1 : ‖(((n:ℝ) + 1)⁻¹)‖ = ((n:ℝ) + 1)⁻¹ := by rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hn1)]
  have e2 : ‖(‖c‖)⁻¹‖ = (‖c‖)⁻¹ := by rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos)]
  rw [hf, norm_smul, norm_smul, norm_smul, e1, e2]
  have hinv : ((n:ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [(n.cast_nonneg : (0:ℝ) ≤ n)])
  have key : ∀ (t a b N : ℝ), 0 < t → a ≤ C → 0 ≤ a → 0 ≤ b → b ≤ 1 → 0 ≤ N → N ≤ 1 →
      t * (a * (b * (t⁻¹ * N))) ≤ C := by
    intro t a b N ht ha ha0 hb0 hb1 hN0 hN1
    rw [show t * (a * (b * (t⁻¹ * N))) = a * (b * N) * (t * t⁻¹) by ring, mul_inv_cancel₀ ht.ne', mul_one]
    calc a * (b * N) ≤ C * (1 * 1) :=
          mul_le_mul ha (mul_le_mul hb1 hN1 hN0 zero_le_one) (mul_nonneg hb0 hN0) (le_trans ha0 ha)
      _ = C := by ring
  exact key _ _ _ _ hpos (hC _) (norm_nonneg _) (inv_nonneg.2 hn1.le) hinv (norm_nonneg _) hN

end LogBump

end Formalism.FourierDecayAlt.P5.HerB
end
end

section

open Set Filter Topology Complex

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

def wZ (f : ℂ → ℂ) (ζ : ℂ) : ℂ := (1 / 2 : ℂ) * (fderiv ℝ f ζ 1 - I * fderiv ℝ f ζ I)

def wZb (f : ℂ → ℂ) (ζ : ℂ) : ℂ := (1 / 2 : ℂ) * (fderiv ℝ f ζ 1 + I * fderiv ℝ f ζ I)

def Hh (TT : ℝ) : Set ℂ := {w | TT < Complex.normSq (Complex.exp w)}

theorem normSq_exp (w : ℂ) : Complex.normSq (Complex.exp w) = Real.exp w.re ^ 2 := by

  first
    | rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
    | simp [Complex.normSq_eq_norm_sq, Complex.norm_exp]

theorem isOpen_Hh (TT : ℝ) : IsOpen (Hh TT) := isOpen_lt continuous_const (Complex.continuous_normSq.comp Complex.continuous_exp)

theorem convex_Hh (TT : ℝ) : Convex ℝ (Hh TT) := by

  intro w1 h1 w2 h2 a b ha hb hab
  simp only [Hh, Set.mem_setOf_eq, normSq_exp] at h1 h2 ⊢
  have hre : (a • w1 + b • w2).re = a * w1.re + b * w2.re := by simp
  rw [hre]
  rcases le_total w1.re w2.re with h | h
  · calc TT < Real.exp w1.re ^ 2 := h1
      _ ≤ Real.exp (a * w1.re + b * w2.re) ^ 2 := by
        have e : a * w1.re + b * w2.re - w1.re = b * (w2.re - w1.re) := by
          rw [show a = 1 - b by linarith]; ring
        have : w1.re ≤ a * w1.re + b * w2.re := by nlinarith [mul_nonneg hb (sub_nonneg.2 h)]
        gcongr
  · calc TT < Real.exp w2.re ^ 2 := h2
      _ ≤ Real.exp (a * w1.re + b * w2.re) ^ 2 := by
        have e : a * w1.re + b * w2.re - w2.re = a * (w1.re - w2.re) := by
          rw [show b = 1 - a by linarith]; ring
        have : w2.re ≤ a * w1.re + b * w2.re := by nlinarith [mul_nonneg ha (sub_nonneg.2 h)]
        gcongr

def bet (α : ℂ → ℂ) (w : ℂ) : ℂ := α (Complex.exp w) * Complex.exp w

def omL : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) :=
  (2 : ℝ) • (ContinuousLinearMap.compL ℝ ℂ ℂ ℝ Complex.imCLM).comp (ContinuousLinearMap.mul ℝ ℂ)

theorem omL_apply (c v : ℂ) : omL c v = 2 * (c * v).im := by

  simp [omL]

def om (α : ℂ → ℂ) (w : ℂ) : ℂ →L[ℝ] ℝ := omL (bet α w)

theorem om_apply (α : ℂ → ℂ) (w v : ℂ) : om α w v = 2 * (bet α w * v).im := omL_apply _ _

theorem bet_periodic (α : ℂ → ℂ) (w : ℂ) (k : ℤ) : bet α (w + (k : ℂ) * (2 * Real.pi * I)) = bet α w := by

  simp only [bet, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end

section

namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section propG

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem eventually_ne_cocompact (c : ℂ) : ∀ᶠ x in cocompact ℂ, x ≠ c := by
  filter_upwards [(isCompact_singleton : IsCompact ({c} : Set ℂ)).compl_mem_cocompact] with x hx
  simpa using hx

theorem eventually_rate_cocompact (σ : ℂ) (C δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x in cocompact ℂ, C * ‖x + σ‖⁻¹ ≤ δ := by
  have h0 : Tendsto (fun x : ℂ => ‖x‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
  have h := h0.eventually_ge_atTop (‖σ‖ + |C| / δ + 1)
  filter_upwards [h] with x hx
  have h1 : |C| / δ + 1 ≤ ‖x + σ‖ := by
    have := norm_sub_norm_le x (-σ)
    rw [norm_neg, sub_neg_eq_add] at this
    linarith
  have hpos : 0 < ‖x + σ‖ := lt_of_lt_of_le (by positivity) h1
  rw [← div_eq_mul_inv, div_le_iff₀ hpos]
  have h2 : |C| = δ * (|C| / δ) := by
    first
    | (field_simp; ring)
    | field_simp
  calc C ≤ |C| := le_abs_self C
    _ = δ * (|C| / δ) := h2
    _ ≤ δ * ‖x + σ‖ := by
        apply mul_le_mul_of_nonneg_left _ hδ.le
        linarith

theorem integral_sq_sub_le {μ : Measure ℂ} {u a : ℂ → H} {ab : ℂ → ℝ} (hu : MemLp u 2 μ) (ha : MemLp a 2 μ)
    (hab : MemLp ab 2 μ) (hd : ∀ᵐ D ∂μ, ‖a D‖ ≤ ab D) :
    ∫ D, ‖u D - a D‖ ^ 2 ∂μ ≤ 2 * ∫ D, ‖u D‖ ^ 2 ∂μ + 2 * ∫ D, ab D ^ 2 ∂μ := by
  have i1 : Integrable (fun D => ‖u D - a D‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (hu.sub ha).aestronglyMeasurable).1 (hu.sub ha)
  have i2 : Integrable (fun D => ‖u D‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu
  have i3 : Integrable (fun D => ab D ^ 2) μ := (memLp_two_iff_integrable_sq hab.aestronglyMeasurable).1 hab
  calc ∫ D, ‖u D - a D‖ ^ 2 ∂μ ≤ ∫ D, (2 * ‖u D‖ ^ 2 + 2 * ab D ^ 2) ∂μ := by
        refine integral_mono_ae i1 ((i2.const_mul 2).add (i3.const_mul 2)) ?_
        filter_upwards [hd] with D hD
        have h1 : ‖u D - a D‖ ≤ ‖u D‖ + ‖a D‖ := norm_sub_le _ _
        have h2 : 0 ≤ ‖a D‖ := norm_nonneg _
        have h3 : 0 ≤ ‖u D - a D‖ := norm_nonneg _
        have e1 : ‖u D - a D‖ ^ 2 ≤ (‖u D‖ + ‖a D‖) ^ 2 := pow_le_pow_left₀ h3 h1 2
        have e2 : ‖a D‖ ^ 2 ≤ ab D ^ 2 := pow_le_pow_left₀ h2 hD 2
        nlinarith [sq_nonneg (‖u D‖ - ‖a D‖)]
    _ = 2 * ∫ D, ‖u D‖ ^ 2 ∂μ + 2 * ∫ D, ab D ^ 2 ∂μ := by
        rw [integral_add (i2.const_mul 2) (i3.const_mul 2), integral_const_mul, integral_const_mul]

variable {ι : Type} {μ : Measure ℂ} {Y : Finset ι} {U A : ι × ℂ → ℂ → H} {N : ℂ → ι → ι → ℂ}

end propG

end

end Formalism.FourierDecayAlt.P.PBK
end

section

open Set Filter Topology MeasureTheory intervalIntegral

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {ω : ℂ → ℂ →L[ℝ] ℝ} {S : Set ℂ} {w₀ : ℂ}

def prim (ω : ℂ → ℂ →L[ℝ] ℝ) (w₀ w : ℂ) : ℝ := ∫ t in (0 : ℝ)..1, ω (w₀ + (t : ℂ) * (w - w₀)) (w - w₀)

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end
