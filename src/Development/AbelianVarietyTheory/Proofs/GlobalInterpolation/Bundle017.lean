module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle013
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle004
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormOneSubConjMul
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormSubOneMulRiemannZetaLe
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle007
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LintegralComplexEqLintegralSqrtMulExp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.ZetaLocal

lemma zeta₁_eq {s : ℂ} (hs : s ≠ 1) : riemannZeta₁ s = (s - 1) * riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul hs, mul_inv_cancel_left₀ (sub_ne_zero.2 hs)]

lemma zeta₁_eq_zero_iff (w : ℂ) : riemannZeta₁ w = 0 ↔ w ≠ 1 ∧ riemannZeta w = 0 := by
  by_cases h : w = 1
  · simp [h]
  · simp [zeta₁_eq h, sub_ne_zero.2 h, h]

lemma order_zeta₁ {w : ℂ} (hw : w ≠ 1) :
    analyticOrderNatAt riemannZeta₁ w = analyticOrderNatAt riemannZeta w := by
  have h1 : riemannZeta₁ =ᶠ[nhds w] (fun s => s - 1) * riemannZeta := by
    filter_upwards [compl_singleton_mem_nhds hw] with s hs using zeta₁_eq hs
  have h2 : AnalyticAt ℂ riemannZeta w :=
    differentiableOn_riemannZeta.analyticAt (compl_singleton_mem_nhds hw)
  have h3 : AnalyticAt ℂ (fun s : ℂ => s - 1) w := by fun_prop
  unfold analyticOrderNatAt
  rw [analyticOrderAt_congr h1, analyticOrderAt_mul h3 h2,
    h3.analyticOrderAt_eq_zero.2 (sub_ne_zero.2 hw), zero_add]

lemma order_shift (c w : ℂ) :
    analyticOrderNatAt (fun z => riemannZeta₁ (c + z)) w
      = analyticOrderNatAt riemannZeta₁ (c + w) := by
  unfold analyticOrderNatAt
  have := analyticOrderAt_comp_of_deriv_ne_zero (f := riemannZeta₁) (g := fun z => c + z)
    (z₀ := w) (by fun_prop) (by simp)
  exact congrArg _ this

lemma logDeriv_zeta₁ {s : ℂ} (hs : s ≠ 1) (h0 : riemannZeta s ≠ 0) :
    deriv riemannZeta₁ s / riemannZeta₁ s = deriv riemannZeta s / riemannZeta s + 1 / (s - 1) := by
  rw [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs, zeta₁_eq hs]
  have := sub_ne_zero.2 hs
  field_simp
  ring

lemma norm_zeta₁_le (t : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖riemannZeta₁ (3/2 + t * I + z)‖ ≤ 5 * (|t| + 2) ^ 2 := by
  have ht := abs_nonneg t
  set w : ℂ := 3/2 + t * I + z with hw
  by_cases h : w = 1
  · rw [h, riemannZeta₁_one, norm_one]; nlinarith
  have hre : 1 / 2 ≤ w.re := by
    have := (abs_le.1 ((abs_re_le_norm z).trans hz)).1
    simp [hw]; linarith
  have htI : ‖(t : ℂ) * I‖ = |t| := by simp
  have h1 : ‖w - 1‖ ≤ |t| + 2 := by
    have : w - 1 = 1/2 + t * I + z := by rw [hw]; ring
    rw [this]
    refine norm_add₃_le.trans ?_
    rw [htI]; norm_num; linarith
  have h2 : ‖w‖ ≤ 2 * (|t| + 2) := by
    refine norm_add₃_le.trans ?_
    rw [htI]; norm_num; linarith
  have h3 := GlobalTheory.ZetaHalfPlane.norm_zeta_sub_le w (by linarith) h
  have h4 : ‖w‖ / w.re ≤ 2 * ‖w‖ := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [norm_nonneg w]
  have e : riemannZeta₁ w = (w - 1) * (riemannZeta w - w / (w - 1)) + w := by
    have := sub_ne_zero.2 h
    rw [zeta₁_eq h]; field_simp; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have h5 : ‖w - 1‖ * ‖riemannZeta w - w / (w - 1)‖ ≤ (|t| + 2) * (4 * (|t| + 2)) :=
    mul_le_mul h1 (by linarith) (norm_nonneg _) (by linarith)
  nlinarith

lemma le_norm_zeta₁ (t : ℝ) : 1 / 6 ≤ ‖riemannZeta₁ (3/2 + t * I)‖ := by
  set w : ℂ := 3/2 + t * I with hw
  have hre : w.re = 3 / 2 := by simp [hw]
  have h : w ≠ 1 := by
    intro h; rw [h] at hre; norm_num at hre
  have h1 := GlobalTheory.LLower.norm_LFunction_ge 1 (1 : DirichletCharacter ℂ 1) w (by rw [hre]; norm_num)
  rw [LFunction_modOne_eq, hre] at h1
  have h2 : 1 / 2 ≤ ‖w - 1‖ := by
    refine le_trans ?_ (re_le_norm _)
    rw [sub_re, hre]; norm_num
  rw [zeta₁_eq h, norm_mul]
  nlinarith

theorem logDeriv_riemannZeta_local : ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (s : ℂ), ‖s - (3/2 + t * I)‖ ≤ 2/3 → s ≠ 1 → riemannZeta s ≠ 0 → {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ w ≠ 1 ∧ riemannZeta w = 0}.Finite ∧ ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) - ∑ᶠ w ∈ {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ w ≠ 1 ∧ riemannZeta w = 0}, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)‖ ≤ C * Real.log (|t| + 2) := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.LogDerivZeros.main (2/3) (5/6) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨9 * C, by positivity, fun t s hs hs1 hs0 => ?_⟩
  have hlow := le_norm_zeta₁ t
  have hup := fun z => norm_zeta₁_le t (z := z)
  set c : ℂ := 3/2 + t * I with hc
  have hd : Differentiable ℂ fun z => riemannZeta₁ (c + z) := by fun_prop
  obtain ⟨⟨hfin, -⟩, H2⟩ := H (fun z => riemannZeta₁ (c + z)) (5 * (|t| + 2) ^ 2)
    (fun z _ => hd.analyticAt z) (by
      simp only [add_zero]
      intro h; rw [h, norm_zero] at hlow; norm_num at hlow)
    (fun z hz => hup z (by simpa using hz))
  have hset : {w : ℂ | ‖w - c‖ ≤ 5/6 ∧ w ≠ 1 ∧ riemannZeta w = 0}
      = (fun z => c + z) '' {w : ℂ | ‖w‖ ≤ 5/6 ∧ riemannZeta₁ (c + w) = 0} := by
    ext w
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨w - c, ⟨h1, by rw [add_sub_cancel]; exact (zeta₁_eq_zero_iff w).2 h2⟩, by simp⟩
    · rintro ⟨z, ⟨h1, h2⟩, rfl⟩
      exact ⟨by simpa using h1, (zeta₁_eq_zero_iff _).1 h2⟩
  rw [hset]
  refine ⟨hfin.image _, ?_⟩
  have H3 := H2 (s - c) hs (by
    simp only [add_sub_cancel]
    exact fun h => hs0 ((zeta₁_eq_zero_iff s).1 h).2)
  rw [finsum_mem_image (add_right_injective c).injOn, ← logDeriv_zeta₁ hs1 hs0]
  have e : (∑ᶠ w ∈ {w : ℂ | ‖w‖ ≤ 5/6 ∧ riemannZeta₁ (c + w) = 0},
      (analyticOrderNatAt riemannZeta (c + w) : ℂ) / (s - (c + w)))
      = ∑ᶠ w ∈ {w : ℂ | ‖w‖ ≤ 5/6 ∧ riemannZeta₁ (c + w) = 0},
      (analyticOrderNatAt (fun z => riemannZeta₁ (c + z)) w : ℂ) / (s - c - w) := by
    refine finsum_mem_congr rfl fun w hw => ?_
    rw [order_shift, order_zeta₁ ((zeta₁_eq_zero_iff _).1 hw.2).1, sub_sub]
  rw [e]
  rw [deriv_comp_const_add] at H3
  simp only [add_sub_cancel, add_zero] at H3
  refine H3.trans ?_
  have ht := abs_nonneg t
  have hT : 2 ≤ |t| + 2 := by linarith
  set T := |t| + 2
  have hl2 : Real.log 2 ≤ Real.log T := Real.log_le_log two_pos hT
  have hl := Real.log_two_gt_d9
  have hn : 0 < ‖riemannZeta₁ c‖ := by linarith
  have h1 : 5 * T ^ 2 / ‖riemannZeta₁ c‖ ≤ T ^ 7 := by
    rw [div_le_iff₀ hn]
    have h5 : (2 : ℝ) ^ 5 ≤ T ^ 5 := by gcongr
    have h6 : 5 ≤ T ^ 5 * ‖riemannZeta₁ c‖ := by nlinarith
    calc 5 * T ^ 2 ≤ (T ^ 5 * ‖riemannZeta₁ c‖) * T ^ 2 := by gcongr
      _ = _ := by ring
  have h2 := Real.log_le_log (by positivity) h1
  rw [Real.log_pow] at h2
  push_cast at h2
  have : 1 + Real.log (5 * T ^ 2 / ‖riemannZeta₁ c‖) ≤ 9 * Real.log T := by linarith
  nlinarith

end GlobalTheory.ZetaLocal
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.ZetaWide

theorem scaled : ∃ C : ℝ, 0 < C ∧ ∀ (F : ℂ → ℂ) (c : ℂ) (M : ℝ), Differentiable ℂ F → F c ≠ 0 →
    (∀ w, ‖w - c‖ ≤ 15/4 → ‖F w‖ ≤ M) →
    ({w : ℂ | ‖w - c‖ ≤ 7/2 ∧ F w = 0}.Finite ∧
      (∑ᶠ w ∈ {w : ℂ | ‖w - c‖ ≤ 7/2 ∧ F w = 0}, (analyticOrderNatAt F w : ℝ))
        ≤ C * (1 + Real.log (M / ‖F c‖))) ∧
    ∀ s : ℂ, ‖s - c‖ ≤ 3 → F s ≠ 0 →
      ‖deriv F s / F s - ∑ᶠ w ∈ {w : ℂ | ‖w - c‖ ≤ 7/2 ∧ F w = 0},
        (analyticOrderNatAt F w : ℂ) / (s - w)‖ ≤ C * (1 + Real.log (M / ‖F c‖)) := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.LogDerivZeros.main (4/5) (14/15) (by norm_num) (by norm_num)
    (by norm_num)
  refine ⟨C, hC, fun F c M hF hc hM => ?_⟩
  set g : ℂ → ℂ := fun z => c + 15/4 * z with hg
  have hgn : ∀ z, ‖g z - c‖ = 15/4 * ‖z‖ := fun z => by simp [hg]
  have hgd : ∀ z, HasDerivAt g (15/4) z := fun z => by
    have := ((hasDerivAt_id z).const_mul (15/4 : ℂ)).const_add c
    rw [mul_one] at this
    exact this
  have hgD : Differentiable ℂ g := fun z => (hgd z).differentiableAt
  have hfD : Differentiable ℂ (F ∘ g) := hF.comp hgD
  have hg0 : g 0 = c := by simp [hg]
  have hf0 : (F ∘ g) 0 = F c := by simp [hg0]
  obtain ⟨⟨h1, h2⟩, h3⟩ := H (F ∘ g) M (fun z _ => hfD.analyticAt z) (by rwa [hf0])
    (fun z hz => hM _ (by
      have : ‖z‖ ≤ 1 := by simpa using hz
      rw [hgn]; linarith))
  rw [hf0] at h2 h3
  have hinj : Function.Injective g := fun a b h => by simpa [hg] using h
  have hsur : ∀ w, g ((w - c) * (4/15)) = w := fun w => by simp only [hg]; ring
  have hset : {w : ℂ | ‖w - c‖ ≤ 7/2 ∧ F w = 0} = g '' {w : ℂ | ‖w‖ ≤ 14/15 ∧ (F ∘ g) w = 0} := by
    ext w
    constructor
    · rintro ⟨ha, hb⟩
      refine ⟨(w - c) * (4/15), ⟨?_, by simp only [Function.comp, hsur, hb]⟩, hsur w⟩
      have := hgn ((w - c) * (4/15))
      rw [hsur] at this
      linarith
    · rintro ⟨z, ⟨ha, hb⟩, rfl⟩
      exact ⟨by rw [hgn]; linarith, hb⟩
  have hord : ∀ z, analyticOrderNatAt (F ∘ g) z = analyticOrderNatAt F (g z) := fun z => by
    unfold analyticOrderNatAt
    rw [analyticOrderAt_comp_of_deriv_ne_zero (hgD.analyticAt z) (by rw [(hgd z).deriv]; norm_num)]
  simp only [hord] at h2 h3
  rw [hset]
  refine ⟨⟨h1.image g, by rwa [finsum_mem_image hinj.injOn]⟩, fun s hs hFs => ?_⟩
  obtain ⟨z, rfl⟩ : ∃ z, s = g z := ⟨_, (hsur s).symm⟩
  rw [hgn] at hs
  have h4 := h3 z (by linarith) hFs
  have hL : 0 ≤ C * (1 + Real.log (M / ‖F c‖)) := (norm_nonneg _).trans h4
  rw [finsum_mem_image hinj.injOn]
  rw [finsum_mem_eq_finite_toFinset_sum _ h1] at h4 ⊢
  have hd : deriv (F ∘ g) z = deriv F (g z) * (15/4) :=
    ((hF (g z)).hasDerivAt.comp z (hgd z)).deriv
  have e : deriv F (g z) / F (g z) - ∑ w ∈ h1.toFinset, (analyticOrderNatAt F (g w) : ℂ) / (g z - g w)
      = (4/15) * (deriv (F ∘ g) z / (F ∘ g) z -
        ∑ w ∈ h1.toFinset, (analyticOrderNatAt F (g w) : ℂ) / (z - w)) := by
    rw [hd, mul_sub, Finset.mul_sum]
    congr 1
    · simp only [Function.comp]; ring
    · refine Finset.sum_congr rfl fun w _ => ?_
      have : g z - g w = 15/4 * (z - w) := by simp only [hg]; ring
      rw [this, div_eq_mul_inv, mul_inv]
      ring
  rw [e, norm_mul]
  have : ‖(4/15 : ℂ)‖ = 4/15 := by simp
  rw [this]
  linarith

theorem zeta₁_eq {s : ℂ} (hs : s ≠ 1) : riemannZeta₁ s = (s - 1) * riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul hs, mul_inv_cancel_left₀ (sub_ne_zero.2 hs)]

theorem order_zeta₁_eq {s : ℂ} (hs : s ≠ 1) :
    analyticOrderNatAt riemannZeta₁ s = analyticOrderNatAt riemannZeta s := by
  unfold analyticOrderNatAt
  have hev : riemannZeta₁ =ᶠ[nhds s] (fun z => z - 1) * riemannZeta := by
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz
    exact zeta₁_eq hz
  have h1 : AnalyticAt ℂ (fun z : ℂ => z - 1) s := by fun_prop
  have h2 : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul h1 h2,
    h1.analyticOrderAt_eq_zero.2 (sub_ne_zero.2 hs), zero_add]

theorem main : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → s ≠ 1 → riemannZeta s ≠ 0 → {w : ℂ | ‖w - (2 + s.im * I)‖ ≤ 7/2 ∧ w ≠ 1 ∧ riemannZeta w = 0}.Finite ∧ (∑ᶠ w ∈ {w : ℂ | ‖w - (2 + s.im * I)‖ ≤ 7/2 ∧ w ≠ 1 ∧ riemannZeta w = 0}, (analyticOrderNatAt riemannZeta w : ℝ)) ≤ C * Real.log (|s.im| + 2) ∧ ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) - ∑ᶠ w ∈ {w : ℂ | ‖w - (2 + s.im * I)‖ ≤ 7/2 ∧ w ≠ 1 ∧ riemannZeta w = 0}, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)‖ ≤ C * Real.log (|s.im| + 2) := by
  obtain ⟨C, hC, H⟩ := scaled
  obtain ⟨B, hB, hBl⟩ := GlobalTheory.ZetaLeft.norm_sub_one_mul_riemannZeta_le
  set K : ℝ := 2 * (B + 1) * 4 ^ 5 with hK
  have hK1 : 1 ≤ K := by rw [hK]; linarith
  have hlK : 0 ≤ Real.log K := Real.log_nonneg hK1
  refine ⟨C * (2 * (1 + Real.log K) + 5), by positivity, fun s hs1 hs2 hs hz => ?_⟩
  set c : ℂ := 2 + s.im * I with hc
  set T : ℝ := |s.im| + 2 with hT
  have hT2 : 2 ≤ T := by have := abs_nonneg s.im; linarith
  have hcre : c.re = 2 := by simp [hc]
  have hc1 : c ≠ 1 := fun h => by rw [h] at hcre; norm_num at hcre
  have hcn : ‖c‖ ≤ T := by
    refine (norm_add_le _ _).trans ?_
    simp [hT, add_comm]
  have hlow : 1 / 2 ≤ ‖riemannZeta₁ c‖ := by
    have h := GlobalTheory.LLower.norm_LFunction_ge 1 1 c (by rw [hcre]; norm_num)
    rw [LFunction_modOne_eq, hcre] at h
    have h' : 1 ≤ ‖c - 1‖ := by
      have := Complex.re_le_norm (c - 1)
      rw [sub_re, hcre, one_re] at this
      linarith
    rw [zeta₁_eq hc1, norm_mul]
    nlinarith
  have hne : riemannZeta₁ c ≠ 0 := norm_pos_iff.1 (by linarith)
  have hup : ∀ w, ‖w - c‖ ≤ 15/4 → ‖riemannZeta₁ w‖ ≤ (B + 1) * (4 * T) ^ 5 := by
    intro w hw
    have hp : 1 ≤ (4 * T) ^ 5 := one_le_pow₀ (by linarith)
    by_cases h1 : w = 1
    · rw [h1, riemannZeta₁_one, norm_one]
      nlinarith
    · have hre : -(7/4 : ℝ) ≤ w.re := by
        have := Complex.abs_re_le_norm (w - c)
        rw [sub_re, hcre] at this
        have := neg_abs_le (w.re - 2)
        linarith
      have hwn : ‖w‖ + 2 ≤ 4 * T := by
        have := norm_add_le (w - c) c
        rw [sub_add_cancel] at this
        linarith
      rw [zeta₁_eq h1]
      refine (hBl w hre h1).trans ?_
      gcongr
      linarith
  obtain ⟨⟨h1, h2⟩, h3⟩ := H riemannZeta₁ c _ differentiable_riemannZeta₁ hne hup
  have hbound : C * (1 + Real.log ((B + 1) * (4 * T) ^ 5 / ‖riemannZeta₁ c‖))
      ≤ C * (2 * (1 + Real.log K) + 5) * Real.log T := by
    have hlT : 1 / 2 ≤ Real.log T := by
      have := Real.log_two_gt_d9
      have := Real.log_le_log (by norm_num) hT2
      linarith
    have ha : (B + 1) * (4 * T) ^ 5 / ‖riemannZeta₁ c‖ ≤ K * T ^ 5 := by
      calc _ ≤ (B + 1) * (4 * T) ^ 5 / (1 / 2) := by gcongr
        _ = K * T ^ 5 := by rw [hK]; ring
    have hb := Real.log_le_log (by positivity) ha
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hb
    rw [mul_assoc]
    gcongr
    push_cast at hb
    nlinarith
  have hset : {w : ℂ | ‖w - c‖ ≤ 7/2 ∧ w ≠ 1 ∧ riemannZeta w = 0}
      = {w : ℂ | ‖w - c‖ ≤ 7/2 ∧ riemannZeta₁ w = 0} := by
    ext w
    by_cases hw : w = 1
    · simp [hw]
    · simp [hw, zeta₁_eq hw, sub_ne_zero.2 hw]
  have hne1 : ∀ w ∈ {w : ℂ | ‖w - c‖ ≤ 7/2 ∧ riemannZeta₁ w = 0}, w ≠ 1 := by
    rintro w ⟨_, hw⟩ rfl
    simp at hw
  have hs0 : s - 1 ≠ 0 := sub_ne_zero.2 hs
  rw [hset]
  refine ⟨h1, ?_, ?_⟩
  · refine le_trans (le_of_eq ?_) (h2.trans hbound)
    exact finsum_mem_congr rfl fun w hw => by rw [order_zeta₁_eq (hne1 w hw)]
  · have hsc : ‖s - c‖ ≤ 3 := by
      have : s - c = ((s.re - 2 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [hc]
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hz1 : riemannZeta₁ s ≠ 0 := by rw [zeta₁_eq hs]; exact mul_ne_zero hs0 hz
    refine le_trans (le_of_eq ?_) ((h3 s hsc hz1).trans hbound)
    congr 2
    · rw [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs, riemannZeta_eq_inv_sub_mul hs]
      field_simp
      ring
    · exact finsum_mem_congr rfl fun w hw => by rw [order_zeta₁_eq (hne1 w hw)]

end GlobalTheory.ZetaWide
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.LLocal

theorem analyticOrderNatAt_comp_const_add (g : ℂ → ℂ) (c w : ℂ) :
    analyticOrderNatAt (fun z => g (c + z)) w = analyticOrderNatAt g (c + w) := by
  unfold analyticOrderNatAt
  congr 1
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := g) (g := fun z : ℂ => c + z) (z₀ := w)
    (by fun_prop) (by simp)
  exact h

theorem logDeriv_LFunction_local : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ (t : ℝ) (s : ℂ), ‖s - (3/2 + t * I)‖ ≤ 2/3 → LFunction χ s ≠ 0 → {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ LFunction χ w = 0}.Finite ∧ ‖deriv (LFunction χ) s / LFunction χ s - ∑ᶠ w ∈ {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ LFunction χ w = 0}, (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w)‖ ≤ C * Real.log (q * (|t| + 2)) := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.LogDerivZeros.main (2/3) (5/6) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨6 * C, by positivity, ?_⟩
  intro q _ χ hχ t s hs hLs
  set c : ℂ := 3/2 + t * I with hc
  have hcre : c.re = 3/2 := by simp [hc]
  have hcn : ‖c‖ ≤ 3/2 + |t| := by
    refine (norm_add_le _ _).trans ?_
    simp
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have ht : 0 ≤ |t| := abs_nonneg t
  have hd : Differentiable ℂ (LFunction χ) := differentiable_LFunction hχ
  have hf : AnalyticOnNhd ℂ (fun z => LFunction χ (c + z)) (Metric.closedBall 0 1) := by
    intro z _
    have : Differentiable ℂ (fun z => LFunction χ (c + z)) := hd.comp (by fun_prop)
    exact this.analyticAt z
  have hlow : 1/3 ≤ ‖LFunction χ (c + 0)‖ := by
    have := GlobalTheory.LLower.norm_LFunction_ge q χ c (by rw [hcre]; norm_num)
    rw [hcre] at this
    rw [add_zero]
    linarith
  have hf0 : LFunction χ (c + 0) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlow
    linarith
  have hM : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      ‖LFunction χ (c + z)‖ ≤ q * (2 * |t| + 5) := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := by simpa using hz
    have hre : 1/2 ≤ (c + z).re := by
      have := (abs_le.1 ((Complex.abs_re_le_norm z).trans hz1)).1
      rw [add_re, hcre]; linarith
    have hn : ‖c + z‖ ≤ |t| + 5/2 := by
      have := norm_add_le c z
      linarith
    refine (GlobalTheory.LGrowth.norm_LFunction_le q χ hχ (c + z) (by linarith)).trans ?_
    rw [div_le_iff₀ (by linarith)]
    calc (q : ℝ) * ‖c + z‖ ≤ q * (|t| + 5/2) := by gcongr
      _ = q * (2 * |t| + 5) * (1/2) := by ring
      _ ≤ _ := by gcongr
  obtain ⟨⟨hfin, -⟩, hb⟩ := H _ _ hf hf0 hM
  have hb' := hb (s - c) hs (by simpa using hLs)
  have hset : {w : ℂ | ‖w - c‖ ≤ 5/6 ∧ LFunction χ w = 0} =
      (fun z => c + z) '' {w : ℂ | ‖w‖ ≤ 5/6 ∧ LFunction χ (c + w) = 0} := by
    ext w
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨w - c, ⟨h1, by simpa using h2⟩, by simp⟩
    · rintro ⟨z, ⟨h1, h2⟩, rfl⟩
      exact ⟨by simpa using h1, h2⟩
  rw [hset]
  refine ⟨hfin.image _, ?_⟩
  rw [finsum_mem_image (fun a _ b _ h => add_left_cancel h)]
  rw [deriv_comp_const_add] at hb'
  simp only [analyticOrderNatAt_comp_const_add, add_sub_cancel, sub_sub] at hb'
  refine hb'.trans ?_
  set X : ℝ := q * (|t| + 2) with hX
  have hX2 : 2 ≤ X := by nlinarith
  have hl2 : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX2
  have hl : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hp : 0 < ‖LFunction χ (c + 0)‖ := by linarith
  have h8 : q * (2 * |t| + 5) / ‖LFunction χ (c + 0)‖ ≤ 2 ^ 3 * X := by
    rw [div_le_iff₀ hp]
    calc (q : ℝ) * (2 * |t| + 5) ≤ 2 ^ 3 * X * (1/3) := by rw [hX]; nlinarith
      _ ≤ _ := by gcongr
  have h9 := Real.log_le_log (by positivity) h8
  rw [Real.log_mul (by norm_num) (by linarith), Real.log_pow] at h9
  push_cast at h9
  have : 1 + Real.log (q * (2 * |t| + 5) / ‖LFunction χ (c + 0)‖) ≤ 6 * Real.log X := by
    linarith
  calc _ ≤ C * (6 * Real.log X) := by gcongr
    _ = _ := by ring

end GlobalTheory.LLocal
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.lintegral_complex_eq_polar_sqrt : ∀ (ε c : ℝ), (ε = 1 ∨ ε = -1) → ∀ g : ℂ → ENNReal, Measurable g → g 0 = 0 → ∫⁻ z, g z = ∫⁻ t : ℝ, ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, (2 : ENNReal)⁻¹ * g ((Real.sqrt (ε * (t - c)) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
  first | exact @GlobalTheory.lintegral_complex_eq_lintegral_sqrt_mul_exp | exact GlobalTheory.lintegral_complex_eq_lintegral_sqrt_mul_exp | (intros; apply GlobalTheory.lintegral_complex_eq_lintegral_sqrt_mul_exp <;> assumption)
end
