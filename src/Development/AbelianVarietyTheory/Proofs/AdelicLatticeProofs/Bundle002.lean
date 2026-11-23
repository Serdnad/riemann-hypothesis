module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.Analysis.Complex.Circle
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.Algebra.Category.Grp.Injective

@[expose] public section

section

open scoped ContDiff

namespace GlobalTheory

section ExpSeries

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {I : Type}

end ExpSeries

open scoped ContDiff in
private lemma norm_smulRight_le_opNorm_mul_norm {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℂ E] (L : V →L[ℝ] ℂ) (w : E) :
    ‖L.smulRight w‖ ≤ ‖L‖ * ‖w‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  rw [ContinuousLinearMap.smulRight_apply, norm_smul]
  calc ‖L h‖ * ‖w‖ ≤ ‖L‖ * ‖h‖ * ‖w‖ :=
        mul_le_mul_of_nonneg_right (L.le_opNorm h) (norm_nonneg _)
    _ = ‖L‖ * ‖w‖ * ‖h‖ := by ring

open scoped ContDiff in
private lemma mul_exp_mul_le_exp_add_one_mul (r R : ℝ) :
    r * Real.exp (R * r) ≤ Real.exp ((R + 1) * r) := by
  calc r * Real.exp (R * r) ≤ Real.exp r * Real.exp (R * r) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp r]) (Real.exp_pos _).le
    _ = Real.exp ((R + 1) * r) := by rw [← Real.exp_add]; ring_nf

open scoped ContDiff in
private lemma summable_norm_smulRight_mul_exp {V E I : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℂ E] (m : I → V →L[ℝ] ℂ) (w : I → E)
    (hw : ∀ R : ℝ, Summable fun i => ‖w i‖ * Real.exp (R * ‖m i‖)) (R : ℝ) :
    Summable fun i => ‖(m i).smulRight (w i)‖ * Real.exp (R * ‖m i‖) := by
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) (hw (R + 1))
  calc ‖(m i).smulRight (w i)‖ * Real.exp (R * ‖m i‖)
      ≤ ‖m i‖ * ‖w i‖ * Real.exp (R * ‖m i‖) :=
        mul_le_mul_of_nonneg_right (norm_smulRight_le_opNorm_mul_norm _ _) (Real.exp_pos _).le
    _ = ‖w i‖ * (‖m i‖ * Real.exp (R * ‖m i‖)) := by ring
    _ ≤ ‖w i‖ * Real.exp ((R + 1) * ‖m i‖) :=
        mul_le_mul_of_nonneg_left (mul_exp_mul_le_exp_add_one_mul _ _) (norm_nonneg _)

open scoped ContDiff in
private lemma norm_cexp_le_exp_mul_opNorm_of_norm_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℂ) {y : V} {r : ℝ} (hy : ‖y‖ ≤ r) :
    ‖Complex.exp (L y)‖ ≤ Real.exp (r * ‖L‖) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  calc (L y).re ≤ ‖L y‖ := Complex.re_le_norm _
    _ ≤ ‖L‖ * ‖y‖ := L.le_opNorm y
    _ ≤ r * ‖L‖ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hy (norm_nonneg _)

open scoped ContDiff in
private lemma hasFDerivAt_tsum_cexp_smul_of_summable_exp {V E I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (m : I → V →L[ℝ] ℂ) (w : I → E)
    (hw : ∀ R : ℝ, Summable fun i => ‖w i‖ * Real.exp (R * ‖m i‖)) (x : V) :
    HasFDerivAt (fun v => ∑' i, Complex.exp (m i v) • w i)
      (∑' i, Complex.exp (m i x) • (m i).smulRight (w i)) x := by
  set r := ‖x‖ + 1
  have hx : x ∈ Metric.ball (0 : V) r := by rw [mem_ball_zero_iff]; simp [r]
  refine hasFDerivAt_tsum_of_isPreconnected (u := fun i => ‖(m i).smulRight (w i)‖ *
      Real.exp (r * ‖m i‖)) (f := fun i v => Complex.exp (m i v) • w i)
    (f' := fun i y => Complex.exp (m i y) • (m i).smulRight (w i))
    (summable_norm_smulRight_mul_exp m w hw r) Metric.isOpen_ball
    (convex_ball _ _).isPreconnected ?_ ?_ hx ?_ hx
  · intro i y _
    refine (((m i).hasFDerivAt.cexp).smul_const (w i)).congr_fderiv ?_
    ext h
    simp [smul_smul]
  · intro i y hy
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_left
      (norm_cexp_le_exp_mul_opNorm_of_norm_le _ (by rw [mem_ball_zero_iff] at hy; exact hy.le)) (norm_nonneg _)
  · refine Summable.of_norm_bounded (hw r) fun i => ?_
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_left (norm_cexp_le_exp_mul_opNorm_of_norm_le _ (by simp [r])) (norm_nonneg _)

open scoped ContDiff in
private lemma contDiff_tsum_cexp_smul_of_summable_exp {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : I → V →L[ℝ] ℂ) (n : ℕ) :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (w : I → E),
      (∀ R : ℝ, Summable fun i => ‖w i‖ * Real.exp (R * ‖m i‖)) →
      ContDiff ℝ n (fun v => ∑' i, Complex.exp (m i v) • w i) := by
  induction n with
  | zero =>
    intro E _ _ _ w hw
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun x =>
      (hasFDerivAt_tsum_cexp_smul_of_summable_exp m w hw x).continuousAt)
  | succ n ih =>
    intro E _ _ _ w hw
    have hd := fun x => hasFDerivAt_tsum_cexp_smul_of_summable_exp m w hw x
    push_cast
    refine contDiff_succ_iff_fderiv.2 ⟨fun x => (hd x).differentiableAt, fun h => by simp at h, ?_⟩
    have hfd : fderiv ℝ (fun v => ∑' i, Complex.exp (m i v) • w i) =
        fun x => ∑' i, Complex.exp (m i x) • (m i).smulRight (w i) :=
      funext fun x => (hd x).fderiv
    rw [hfd]
    exact ih (V →L[ℝ] E) (fun i => (m i).smulRight (w i))
      (summable_norm_smulRight_mul_exp m w hw)


open scoped ContDiff in
theorem _root_.GlobalTheory.expSeries_contDiff_and_hasDerivAt :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (I : Type) (c : I → ℂ)
      (m : I → V →L[ℝ] ℂ), (∀ R : ℝ, Summable fun i => ‖c i‖ * Real.exp (R * ‖m i‖)) →
      ContDiff ℝ ∞ (fun v : V => ∑' i, c i * Complex.exp (m i v)) ∧
        ∀ z : V, Summable (fun i => c i * m i z) ∧
          HasDerivAt (fun t : ℝ => ∑' i, c i * Complex.exp (m i (t • z)))
            (∑' i, c i * m i z) 0 := by
  intro V _ _ I c m hc
  have hfun : (fun v : V => ∑' i, c i * Complex.exp (m i v)) =
      fun v => ∑' i, Complex.exp (m i v) • c i :=
    funext fun v => tsum_congr fun i => by rw [smul_eq_mul, mul_comm]
  have hz : ∀ z : V, Summable fun i => c i * m i z := by
    intro z
    refine Summable.of_norm_bounded ((hc 1).mul_left ‖z‖) fun i => ?_
    rw [norm_mul, one_mul]
    have h1 : 0 ≤ ‖c i‖ * ‖z‖ * (Real.exp ‖m i‖ - ‖m i‖) :=
      mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (by linarith [Real.add_one_le_exp ‖m i‖])
    have h2 : ‖c i‖ * ‖m i z‖ ≤ ‖c i‖ * (‖m i‖ * ‖z‖) :=
      mul_le_mul_of_nonneg_left ((m i).le_opNorm z) (norm_nonneg _)
    nlinarith
  refine ⟨?_, fun z => ⟨hz z, ?_⟩⟩
  · rw [hfun]
    exact contDiff_infty.2 fun n => contDiff_tsum_cexp_smul_of_summable_exp m n ℂ c hc
  · have hF := hasFDerivAt_tsum_cexp_smul_of_summable_exp m c hc (0 : V)
    have hl := (hasDerivAt_id (0 : ℝ)).smul_const z
    have h := hF.comp_hasDerivAt_of_eq (0 : ℝ) hl (zero_smul ℝ z).symm
    have hS : Summable fun i => (m i).smulRight (c i) := by
      refine Summable.of_norm ?_
      simpa using summable_norm_smulRight_mul_exp m c hc 0
    have hS' : Summable fun i => Complex.exp (m i 0) • (m i).smulRight (c i) := by
      simpa using hS
    have hfeq : (fun t : ℝ => ∑' i, c i * Complex.exp (m i (t • z))) =
        ((fun v => ∑' i, Complex.exp (m i v) • c i) ∘ fun y => id y • z) :=
      funext fun t => tsum_congr fun i => by simp [mul_comm]
    rw [hfeq]
    refine h.congr_deriv ?_
    have happ := (hS'.hasSum.mapL (ContinuousLinearMap.apply ℝ ℂ ((1 : ℝ) • z))).tsum_eq
    simp only [ContinuousLinearMap.apply_apply] at happ
    rw [← happ]
    exact tsum_congr fun i => by simp [mul_comm]

end GlobalTheory
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory.LogEulerSeries

theorem hasSum_neg_log_succ {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => z ^ (k + 1) / ((k : ℂ) + 1)) (-Complex.log (1 - z)) := by
  have h := Complex.hasSum_taylorSeries_neg_log hz
  have h2 := (hasSum_nat_add_iff' 1).mpr h
  simpa using h2

theorem hasSum_prod_neg_log {ι : Type} (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1 / 2)
    (hs : Summable fun i => ‖z i‖) :
    HasSum (fun p : ι × ℕ => z p.1 ^ (p.2 + 1) / ((p.2 : ℂ) + 1))
      (∑' i, -Complex.log (1 - z i)) := by
  have hsum : Summable (fun p : ι × ℕ => z p.1 ^ (p.2 + 1) / ((p.2 : ℂ) + 1)) := by
    have hb : Summable (fun p : ι × ℕ => ‖z p.1‖ * ((1 / 2 : ℝ) ^ p.2)) :=
      hs.mul_of_nonneg summable_geometric_two (fun i => norm_nonneg _) (fun k => by positivity)
    refine Summable.of_norm_bounded hb ?_
    rintro ⟨i, k⟩
    simp only
    have h1 : (1 : ℝ) ≤ ‖(k : ℂ) + 1‖ := by
      have : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_natCast]
      exact_mod_cast Nat.le_add_left 1 k
    rw [norm_div, norm_pow, pow_succ, mul_comm]
    calc ‖z i‖ * ‖z i‖ ^ k / ‖(k : ℂ) + 1‖ ≤ ‖z i‖ * ‖z i‖ ^ k := div_le_self (by positivity) h1
      _ ≤ ‖z i‖ * (1 / 2 : ℝ) ^ k := by gcongr; exact hz i
  have hf : ∀ i, HasSum (fun k : ℕ => z i ^ (k + 1) / ((k : ℂ) + 1)) (-Complex.log (1 - z i)) :=
    fun i => hasSum_neg_log_succ (by linarith [hz i])
  have h3 := hsum.hasSum.prod_fiberwise hf
  rw [h3.tsum_eq]
  exact hsum.hasSum

theorem hasSum_one {ι : Type} (N : ι → ℕ) (c : ι → ℂ) (hN : ∀ i, 2 ≤ N i) (hc : ∀ i, ‖c i‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) (hsum : Summable fun i => (N i : ℝ) ^ (-s.re)) :
    HasSum (fun p : ι × ℕ => c p.1 ^ (p.2 + 1) / ((p.2 : ℂ) + 1) *
        Complex.exp (-((((p.2 : ℝ) + 1) * Real.log (N p.1) : ℝ) : ℂ) * s))
      (∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))) := by
  have hpos : ∀ i, 0 < N i := fun i => by have := hN i; omega
  have hn : ∀ i, ‖c i * ((N i : ℕ) : ℂ) ^ (-s)‖ ≤ (N i : ℝ) ^ (-s.re) := fun i => by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (hpos i), Complex.neg_re]
    exact mul_le_of_le_one_left (by positivity) (hc i)
  have h := hasSum_prod_neg_log (fun i => c i * ((N i : ℕ) : ℂ) ^ (-s)) (fun i => by
    refine (hn i).trans ?_
    have h2 : (2 : ℝ) ≤ N i := by exact_mod_cast hN i
    calc (N i : ℝ) ^ (-s.re) ≤ (N i : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = 1 / (N i : ℝ) := by rw [Real.rpow_neg_one, one_div]
      _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2)
    (Summable.of_nonneg_of_le (fun i => norm_nonneg _) hn hsum)
  convert h using 2 with p
  obtain ⟨i, k⟩ := p
  have hne : ((N i : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (hpos i).ne'
  simp only
  rw [mul_pow, Complex.cpow_def_of_ne_zero hne, ← Complex.exp_nat_mul, ← Complex.natCast_log]
  push_cast
  rw [show ((k : ℂ) + 1) * (Complex.log (N i) * -s) = -(((k : ℂ) + 1) * Complex.log (N i)) * s by ring]
  ring

theorem hasSum_log_zeta_sq_mul : ∀ (ι : Type) (N : ι → ℕ) (c : ι → ℂ), (∀ i, 2 ≤ N i) → (∀ i, ‖c i‖ ≤ 1) → (∀ σ : ℝ, 1 < σ → Summable fun i => (N i : ℝ) ^ (-σ)) → ∀ s : ℂ, 1 < s.re → HasSum (fun p : ι × ℕ => (((2 + 2 * (c p.1 ^ (p.2 + 1)).re) / ((p.2 : ℝ) + 1) : ℝ) : ℂ) * Complex.exp (-((((p.2 : ℝ) + 1) * Real.log (N p.1) : ℝ) : ℂ) * s)) (2 * (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-s))) + (∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))) + (∑' i, -Complex.log (1 - starRingEnd ℂ (c i) * ((N i : ℕ) : ℂ) ^ (-s)))) := by
  intro ι N c hN hc hsum s hs
  have h1 := hasSum_one N (fun _ => 1) hN (fun _ => by simp) s hs (hsum _ hs)
  have h2 := hasSum_one N c hN hc s hs (hsum _ hs)
  have h3 := hasSum_one N (fun i => starRingEnd ℂ (c i)) hN (fun i => by simpa using hc i) s hs
    (hsum _ hs)
  have h := ((h1.mul_left 2).add h2).add h3
  convert h using 1
  funext p
  revert p
  rintro ⟨i, k⟩
  simp only
  generalize Complex.exp _ = E
  rw [← map_pow]
  have := Complex.add_conj (c i ^ (k + 1))
  rw [Complex.ofReal_div, Complex.ofReal_add, ← this]
  push_cast
  ring

end GlobalTheory.LogEulerSeries
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

theorem eulerTerm_norm_le_rpow (n : ℕ) (hn : 2 ≤ n) (c s : ℂ) (hc : ‖c‖ ≤ 1) :
    ‖c * (n : ℂ) ^ (-s)‖ ≤ (n : ℝ) ^ (-s.re) := by
  have hn0 : 0 < n := by omega
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn0, Complex.neg_re]
  have : (0 : ℝ) ≤ (n : ℝ) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  calc ‖c‖ * (n : ℝ) ^ (-s.re) ≤ 1 * (n : ℝ) ^ (-s.re) := by gcongr
    _ = (n : ℝ) ^ (-s.re) := one_mul _

theorem eulerTerm_norm_le_half (n : ℕ) (hn : 2 ≤ n) (c s : ℂ) (hc : ‖c‖ ≤ 1) (hs : 1 < s.re) :
    ‖c * (n : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  refine (eulerTerm_norm_le_rpow n hn c s hc).trans ?_
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  calc (n : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-s.re) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) h2 (by linarith)
    _ ≤ (2 : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num

theorem one_sub_re_pos_of_norm_le_half (z : ℂ) (hz : ‖z‖ ≤ 1 / 2) : 0 < (1 - z).re := by
  rw [Complex.sub_re, Complex.one_re]
  have := Complex.re_le_norm z
  linarith

theorem eulerProduct_eq_exp_and_pos :
    ∀ (ι : Type) (N : ι → ℕ) (c : ι → ℂ), (∀ i, 2 ≤ N i) → (∀ i, ‖c i‖ ≤ 1) → (∀ σ : ℝ, 1 < σ → Summable fun i => (N i : ℝ) ^ (-σ)) → (∀ s : ℂ, 1 < s.re → Summable (fun i => -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))) ∧ HasProd (fun i => (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))⁻¹) (Complex.exp (∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))))) ∧ ∀ e : ι ≃ ι, (∀ i, N (e i) = N i) → (∀ i, c (e i) = starRingEnd ℂ (c i)) → ∀ s : ℂ, 1 < s.re → s.im = 0 → (Complex.exp (∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)))).im = 0 ∧ 0 < (Complex.exp (∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)))).re := by
  intro ι N c hN hc hsum
  have hsmall : ∀ s : ℂ, 1 < s.re → ∀ i, ‖c i * ((N i : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 2 :=
    fun s hs i => eulerTerm_norm_le_half (N i) (hN i) (c i) s (hc i) hs
  have hne : ∀ s : ℂ, 1 < s.re → ∀ i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)) ≠ 0 := by
    intro s hs i h
    have := one_sub_re_pos_of_norm_le_half _ (hsmall s hs i)
    rw [h, Complex.zero_re] at this
    exact lt_irrefl 0 this
  have hsummable : ∀ s : ℂ, 1 < s.re →
      Summable (fun i => -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))) := by
    intro s hs
    refine Summable.of_norm_bounded ((hsum s.re hs).mul_left (3 / 2)) (fun i => ?_)
    rw [norm_neg, sub_eq_add_neg]
    refine (Complex.norm_log_one_add_half_le_self (by rw [norm_neg]; exact hsmall s hs i)).trans ?_
    rw [norm_neg]
    gcongr
    exact eulerTerm_norm_le_rpow (N i) (hN i) (c i) s (hc i)
  refine ⟨fun s hs => ⟨hsummable s hs, ?_⟩, ?_⟩
  · convert (hsummable s hs).hasSum.cexp using 1
    funext i
    simp only [Function.comp, Complex.exp_neg, Complex.exp_log (hne s hs i)]
  · intro e hNe hce s hs him
    have hsre : s = ((s.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    have hreal : ∀ i, starRingEnd ℂ (((N i : ℕ) : ℂ) ^ (-s)) = ((N i : ℕ) : ℂ) ^ (-s) := by
      intro i
      rw [hsre, ← Complex.ofReal_neg, ← Complex.ofReal_natCast,
        ← Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.conj_ofReal]
    have hterm : ∀ i, starRingEnd ℂ (-Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))) =
        -Complex.log (1 - c (e i) * ((N (e i) : ℕ) : ℂ) ^ (-s)) := by
      intro i
      have harg : (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)).arg ≠ Real.pi := by
        rw [Ne, Complex.arg_eq_pi_iff]
        have := one_sub_re_pos_of_norm_le_half _ (hsmall s hs i)
        intro h
        linarith [h.1]
      rw [map_neg, ← Complex.log_conj _ harg, map_sub, map_one, map_mul, hreal, hce, hNe]
    set S := ∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)) with hS
    have hconj : starRingEnd ℂ S = S := by
      rw [hS, Complex.conj_tsum]
      simp_rw [hterm]
      exact Equiv.tsum_eq e (fun i => -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)))
    have hSim : S.im = 0 := Complex.conj_eq_iff_im.mp hconj
    rw [Complex.exp_im, Complex.exp_re, hSim, Real.sin_zero, Real.cos_zero, mul_zero, mul_one]
    exact ⟨rfl, Real.exp_pos _⟩

end GlobalTheory
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory


open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
theorem _root_.GlobalTheory.existsUnique_isPrincipal_mul_classRep {K : Type} [Field K] [NumberField K]
    (b : ClassGroup (𝓞 K) → (Ideal (𝓞 K))⁰)
    (hb : Function.Bijective (fun c => ClassGroup.mk0 (b c))) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ∃! c, (I * (b c : Ideal (𝓞 K))).IsPrincipal := by
  have hI0 : I ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero hI
  have key : ∀ c, (I * (b c : Ideal (𝓞 K))).IsPrincipal ↔
      ClassGroup.mk0 (b c) = (ClassGroup.mk0 ⟨I, hI0⟩)⁻¹ := by
    intro c
    rw [eq_inv_iff_mul_eq_one, mul_comm, ← map_mul]
    rw [ClassGroup.mk0_eq_one_iff]
    rfl
  obtain ⟨c, hc⟩ := hb.2 (ClassGroup.mk0 ⟨I, hI0⟩)⁻¹
  refine ⟨c, (key c).2 hc, fun c' hc' => hb.1 ?_⟩
  simp only
  rw [(key c').1 hc']
  exact hc.symm


open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
theorem _root_.GlobalTheory.tsum_isPrincipal_mul_eq {K : Type} [Field K] [NumberField K]
    (B : Ideal (𝓞 K)) (hB : B ≠ ⊥) (F : Ideal (𝓞 K) → ℂ) :
    ∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (I * B).IsPrincipal}, F (I * B) =
      ∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ B}, F J := by
  let e : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (I * B).IsPrincipal} →
      {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ B} :=
    fun I => ⟨I.1 * B, mul_ne_zero I.2.1 hB, I.2.2, Ideal.mul_le_inf.trans inf_le_right⟩
  have he : Function.Bijective e := by
    constructor
    · intro I I' h
      have h' : I.1 * B = I'.1 * B := congrArg Subtype.val h
      exact Subtype.ext (mul_right_cancel₀ hB h')
    · intro J
      obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.2 J.2.2.2
      have hI0 : I ≠ ⊥ := by
        rintro rfl
        exact J.2.1 (by rw [hI, Ideal.mul_bot])
      refine ⟨⟨I, hI0, ?_⟩, Subtype.ext ?_⟩
      · rw [mul_comm, ← hI]; exact J.2.2.1
      · show I * B = J.1
        rw [hI, mul_comm]
  exact (Equiv.ofBijective e he).tsum_eq (fun J => F J.1)

end GlobalTheory
end

section

open scoped Topology

namespace GlobalTheory

theorem circle_hom_extend_of_injective {A B : Type} [CommGroup A] [CommGroup B] (i : A →* B)
    (hi : Function.Injective i) (ψ : A →* Circle) : ∃ χ : B →* Circle, ∀ a, χ (i a) = ψ a := by
  letI : DivisibleBy (Additive Circle) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn u => by
    obtain ⟨t, ht⟩ := Circle.exp_surjective (Additive.toMul u)
    refine ⟨Additive.ofMul (Circle.exp (t / n)), ?_⟩
    apply Additive.toMul.injective
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    simp only [toMul_nsmul, toMul_ofMul]
    rw [← ht, ← Circle.exp_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ hn']
  letI : DivisibleBy (Additive Circle) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨ρ, hρ⟩ := (Module.Baer.of_divisible (Additive Circle)).extension_property_addMonoidHom
    (MonoidHom.toAdditive i) hi (MonoidHom.toAdditive ψ)
  refine ⟨MonoidHom.toAdditive.symm ρ, fun a => ?_⟩
  exact congrArg Additive.toMul (DFunLike.congr_fun hρ (Additive.ofMul a))

theorem exists_continuous_circle_char_extension :
    ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] (H N : Subgroup G) (ψ : H →* Circle), IsOpen (H : Set G) → Continuous ψ → (∀ x : H, (x : G) ∈ N → ψ x = 1) → ∃ χ : G →* Circle, Continuous χ ∧ (∀ x ∈ N, χ x = 1) ∧ ∀ x : H, χ x = ψ x := by
  intro G _ _ _ H N ψ hH hψ hN
  let f : H →* G ⧸ N := (QuotientGroup.mk' N).comp H.subtype
  have hker : f.ker ≤ ψ.ker := fun x hx => by
    rw [MonoidHom.mem_ker] at hx ⊢
    exact hN x ((QuotientGroup.eq_one_iff _).1 hx)
  obtain ⟨χ₀, hχ₀⟩ := circle_hom_extend_of_injective (QuotientGroup.kerLift f)
    (QuotientGroup.kerLift_injective f) (QuotientGroup.lift f.ker ψ hker)
  have hx : ∀ x : H, (χ₀.comp (QuotientGroup.mk' N)) x = ψ x := fun x => hχ₀ (QuotientGroup.mk x)
  refine ⟨χ₀.comp (QuotientGroup.mk' N), ?_, fun x hxN => ?_, hx⟩
  · refine continuous_of_continuousAt_one _ ?_
    have hc : ContinuousOn (χ₀.comp (QuotientGroup.mk' N)) (H : Set G) := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact hψ.congr fun x => (hx x).symm
    exact hc.continuousAt (hH.mem_nhds H.one_mem)
  · have : QuotientGroup.mk' N x = 1 := (QuotientGroup.eq_one_iff _).2 hxN
    rw [MonoidHom.comp_apply, this, map_one]

end GlobalTheory
end
