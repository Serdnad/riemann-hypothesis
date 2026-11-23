module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.RingTheory.RootsOfUnity.Complex

@[expose] public section

section

open Complex Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem exr_ord (f h : ℂ → ℂ) (Zb : Finset ℂ) (m : ℂ → ℕ) (S : Set ℂ) (hS : IsOpen S)
    (hh : DifferentiableOn ℂ h S) (hfac : ∀ z ∈ S, f z = (∏ ρ ∈ Zb, (z - ρ) ^ m ρ) * h z)
    (ρ : ℂ) (hρ : ρ ∈ Zb) (hρS : ρ ∈ S) (hhρ : h ρ ≠ 0) : analyticOrderNatAt f ρ = m ρ := by
  classical
  have hne : ∀ ρ' ∈ Zb.erase ρ, (ρ - ρ') ^ m ρ' ≠ 0 := fun ρ' h' =>
    pow_ne_zero _ (sub_ne_zero.2 fun e => (Finset.ne_of_mem_erase h') e.symm)
  have hgD : DifferentiableOn ℂ (fun z => (∏ ρ' ∈ Zb.erase ρ, (z - ρ') ^ m ρ') * h z) S :=
    (DifferentiableOn.fun_finsetProd fun ρ' _ => (differentiableOn_id.sub_const ρ').pow _).mul hh
  have hgA := hgD.analyticAt (hS.mem_nhds hρS)
  have hg0 : (∏ ρ' ∈ Zb.erase ρ, (ρ - ρ') ^ m ρ') * h ρ ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 hne) hhρ
  have heq : ∀ z ∈ S, f z = (z - ρ) ^ m ρ * ((∏ ρ' ∈ Zb.erase ρ, (z - ρ') ^ m ρ') * h z) := by
    intro z hz
    rw [hfac z hz, ← Finset.mul_prod_erase Zb (fun ρ' => (z - ρ') ^ m ρ') hρ, mul_assoc]
  have hfA : AnalyticAt ℂ f ρ :=
    (((analyticAt_id.sub analyticAt_const).pow (m ρ)).mul hgA).congr
      (Filter.eventually_of_mem (hS.mem_nhds hρS) fun z hz => (heq z hz).symm)
  have hord : analyticOrderAt f ρ = (m ρ : ℕ∞) := by
    rw [hfA.analyticOrderAt_eq_natCast]
    exact ⟨_, hgA, hg0, Filter.eventually_of_mem (hS.mem_nhds hρS) fun z hz => by rw [heq z hz, smul_eq_mul]⟩
  simp [analyticOrderNatAt, hord]

theorem exr_logDeriv (f h : ℂ → ℂ) (Zb : Finset ℂ) (m : ℂ → ℕ) (S : Set ℂ) (hS : IsOpen S)
    (hh : DifferentiableOn ℂ h S) (hfac : ∀ z ∈ S, f z = (∏ ρ ∈ Zb, (z - ρ) ^ m ρ) * h z)
    (w : ℂ) (hwS : w ∈ S) (hwZ : w ∉ Zb) (hhw : h w ≠ 0) :
    deriv f w / f w = (∑ ρ ∈ Zb, (m ρ : ℂ) / (w - ρ)) + deriv h w / h w := by
  classical
  have hPd : ∀ s : Finset ℂ, w ∉ s → HasDerivAt (fun z => ∏ ρ ∈ s, (z - ρ) ^ m ρ)
      ((∏ ρ ∈ s, (w - ρ) ^ m ρ) * ∑ ρ ∈ s, (m ρ : ℂ) / (w - ρ)) w := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simpa using hasDerivAt_const w (1 : ℂ)
    | insert a s ha ih =>
      intro hw
      have hwa : w - a ≠ 0 := sub_ne_zero.2 fun e => hw (e ▸ Finset.mem_insert_self a s)
      have ih' := ih fun e => hw (Finset.mem_insert_of_mem e)
      have hm := (((hasDerivAt_id' w).sub_const a).pow (m a)).mul ih'
      simp only [Finset.prod_insert ha, Finset.sum_insert ha]
      refine hm.congr_deriv ?_
      simp only [Pi.pow_apply]
      rcases Nat.eq_zero_or_pos (m a) with h0 | hpos
      · rw [h0]; simp
      · obtain ⟨k, hk⟩ : ∃ k, m a = k + 1 := ⟨m a - 1, by omega⟩
        rw [hk, Nat.add_sub_cancel]
        push_cast
        field_simp
        ring
  have hPne : (∏ ρ ∈ Zb, (w - ρ) ^ m ρ) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun ρ hρ => pow_ne_zero _ (sub_ne_zero.2 fun e => hwZ (e ▸ hρ))
  have hhd : HasDerivAt h (deriv h w) w := (hh.differentiableAt (hS.mem_nhds hwS)).hasDerivAt
  have hprod := (hPd Zb hwZ).mul hhd
  have hev : f =ᶠ[𝓝 w] fun z => (∏ ρ ∈ Zb, (z - ρ) ^ m ρ) * h z :=
    Filter.eventually_of_mem (hS.mem_nhds hwS) hfac
  have hd : deriv f w = _ := hev.deriv_eq.trans hprod.deriv
  rw [hd, hfac w hwS]
  field_simp

theorem exr_term (m e c w ρ y : ℂ) (hw : w ≠ 0) (hw1 : w - 1 ≠ 0) (hwρ : w - ρ ≠ 0)
    (hρ : ρ ≠ 0) (hρ1 : ρ - 1 ≠ 0) :
    -(m / (w - ρ)) * (e / w / (w - 1)) + m / (1 - ρ) * y / (w - 1) - (-m * (c / (ρ * (ρ - 1)))) / (w - ρ)
      + m / (ρ - 1) * ((e / w - c / ρ) / (w - ρ) - (e / w - y) / (w - 1)) = 0 := by
  have hρ1' : 1 - ρ ≠ 0 := fun e => hρ1 (by linear_combination -e)
  field_simp
  ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section

open Finset Complex Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.T2

theorem rootSum (N : ℕ) (hN : 0 < N) (t : ℕ) (ht : t < N) :
    ∑ k ∈ range N, (cexp (2 * Real.pi * I / N) ^ k) ^ t = if t = 0 then (N : ℂ) else 0 := by

  have hprim := Complex.isPrimitiveRoot_exp N (by omega)
  split_ifs with ht0
  · subst ht0
    simp
  · have hx : cexp (2 * Real.pi * I / N) ^ t ≠ 1 := hprim.pow_ne_one_of_pos_of_lt (by omega) ht
    have h1 : ∀ k, (cexp (2 * Real.pi * I / N) ^ k) ^ t = (cexp (2 * Real.pi * I / N) ^ t) ^ k := fun k => pow_right_comm _ _ _
    simp_rw [h1]
    have hxN : (cexp (2 * Real.pi * I / N) ^ t) ^ N = 1 := by rw [pow_right_comm, hprim.pow_eq_one, one_pow]
    rw [geom_sum_eq hx, hxN, sub_self, zero_div]

theorem rootNorm (N : ℕ) (_hN : 0 < N) (k : ℕ) : ‖cexp (2 * Real.pi * I / N) ^ k‖ = 1 := by

  rw [norm_pow, (Complex.isPrimitiveRoot_exp N (by omega)).norm'_eq_one (by omega), one_pow]

theorem rootPowN (N : ℕ) (hN : 0 < N) (k : ℕ) : (cexp (2 * Real.pi * I / N) ^ k) ^ N = 1 := by

  rw [pow_right_comm, (Complex.isPrimitiveRoot_exp N (by omega)).pow_eq_one, one_pow]

theorem rootAvg (N : ℕ) (j : ℕ) (hj : 1 ≤ j) (hjN : j < N) (y : ℂ) (hy : ‖y‖ ≠ 1) :
    ∑ k ∈ range N, (y * cexp (2 * Real.pi * I / N) ^ k) ^ j / (1 - y * cexp (2 * Real.pi * I / N) ^ k)
      = N * (y ^ N / (1 - y ^ N)) := by

  have hN : 0 < N := by omega
  have hyN : 1 - y ^ N ≠ 0 := by
    intro h
    have h2 : y ^ N = 1 := by linear_combination -h
    have h3 : ‖y‖ ^ N = 1 := by rw [← norm_pow, h2, norm_one]
    exact hy ((pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).mp h3)
  have hxk : ∀ k, 1 - y * cexp (2 * Real.pi * I / N) ^ k ≠ 0 := by
    intro k h
    have h2 : y * cexp (2 * Real.pi * I / N) ^ k = 1 := by linear_combination -h
    apply hy
    have h3 := congrArg norm h2
    rwa [norm_mul, rootNorm N hN k, mul_one, norm_one] at h3
  have hS : ∀ s : ℕ, ∑ k ∈ range N, (cexp (2 * Real.pi * I / N) ^ k) ^ s = if s % N = 0 then (N : ℂ) else 0 := by
    intro s
    have h1 : ∀ k, (cexp (2 * Real.pi * I / N) ^ k) ^ s = (cexp (2 * Real.pi * I / N) ^ k) ^ (s % N) := by
      intro k
      conv_lhs => rw [← Nat.div_add_mod s N, pow_add, pow_mul, rootPowN N hN k, one_pow, one_mul]
    simp_rw [h1]
    rw [rootSum N hN _ (Nat.mod_lt _ hN)]
  have hterm : ∀ k, (y * cexp (2 * Real.pi * I / N) ^ k) ^ j / (1 - y * cexp (2 * Real.pi * I / N) ^ k) =
      (∑ m ∈ range N, y ^ (j + m) * (cexp (2 * Real.pi * I / N) ^ k) ^ (j + m)) / (1 - y ^ N) := by
    intro k
    rw [div_eq_div_iff (hxk k) hyN]
    have hg := mul_neg_geom_sum (y * cexp (2 * Real.pi * I / N) ^ k) N
    have hxN : (y * cexp (2 * Real.pi * I / N) ^ k) ^ N = y ^ N := by rw [mul_pow, rootPowN N hN k, mul_one]
    rw [hxN] at hg
    have h1 : ∑ m ∈ range N, y ^ (j + m) * (cexp (2 * Real.pi * I / N) ^ k) ^ (j + m) =
        (y * cexp (2 * Real.pi * I / N) ^ k) ^ j * ∑ i ∈ range N, (y * cexp (2 * Real.pi * I / N) ^ k) ^ i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    rw [h1, ← hg]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.sum_div, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hS]
  rw [Finset.sum_eq_single (N - j)]
  · rw [if_pos (by rw [Nat.add_sub_cancel' hjN.le, Nat.mod_self]), Nat.add_sub_cancel' hjN.le]
    ring
  · intro m hm hne
    rw [Finset.mem_range] at hm
    rw [if_neg, mul_zero]
    by_cases hlt : j + m < N
    · rw [Nat.mod_eq_of_lt hlt]
      omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  · intro h
    exfalso
    simp at h
    omega

theorem ratioLim (y : ℂ) (hy : ‖y‖ ≠ 1) :
    Tendsto (fun N : ℕ => y ^ N / (1 - y ^ N)) atTop (𝓝 (if 1 < ‖y‖ then (-1 : ℂ) else 0)) := by

  split_ifs with h
  · have hz : ‖y⁻¹‖ < 1 := by
      rw [norm_inv]
      exact inv_lt_one_of_one_lt₀ h
    have h1 := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz
    have h2 : Tendsto (fun N : ℕ => 1 / (y⁻¹ ^ N - 1)) atTop (𝓝 (1 / (0 - 1))) :=
      tendsto_const_nhds.div (h1.sub tendsto_const_nhds) (by norm_num)
    have hy0 : y ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h
      linarith
    have h3 : (fun N : ℕ => y ^ N / (1 - y ^ N)) = (fun N : ℕ => 1 / (y⁻¹ ^ N - 1)) := by
      funext N
      have hyN : y ^ N ≠ 0 := pow_ne_zero _ hy0
      rw [inv_pow, show (y ^ N)⁻¹ - 1 = (1 - y ^ N) / y ^ N by field_simp, one_div_div]
    have h4 : (-1 : ℂ) = 1 / (0 - 1) := by norm_num
    rw [h3, h4]
    exact h2
  · have hlt : ‖y‖ < 1 := lt_of_le_of_ne (not_lt.mp h) hy
    have h1 := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt
    have h2 : Tendsto (fun N : ℕ => y ^ N / (1 - y ^ N)) atTop (𝓝 (0 / (1 - 0))) :=
      h1.div (tendsto_const_nhds.sub h1) (by norm_num)
    rw [show (0 : ℂ) / (1 - 0) = 0 by norm_num] at h2
    exact h2

theorem avgLimit {n : ℕ} (y : Fin n → ℂ) (hy : ∀ i, ‖y i‖ ≠ 1) (j : ℕ) (hj : 1 ≤ j) (K : ℝ)
    (hK : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖∑ i, (y i * ζ) ^ j / (1 - y i * ζ)‖ ≤ K) :
    ((univ.filter (fun i => 1 < ‖y i‖)).card : ℝ) ≤ K := by

  classical
  have hbound : ∀ N : ℕ, j < N → ‖∑ i, y i ^ N / (1 - y i ^ N)‖ ≤ K := by
    intro N hjN
    have hN : 0 < N := by omega
    have h1 : ∑ k ∈ range N, ∑ i, (y i * cexp (2 * Real.pi * I / N) ^ k) ^ j /
        (1 - y i * cexp (2 * Real.pi * I / N) ^ k) = N * ∑ i, y i ^ N / (1 - y i ^ N) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => rootAvg N j hj hjN (y i) (hy i))
    have h2 : ‖∑ k ∈ range N, ∑ i, (y i * cexp (2 * Real.pi * I / N) ^ k) ^ j /
        (1 - y i * cexp (2 * Real.pi * I / N) ^ k)‖ ≤ N * K := by
      calc _ ≤ ∑ k ∈ range N, ‖∑ i, (y i * cexp (2 * Real.pi * I / N) ^ k) ^ j /
            (1 - y i * cexp (2 * Real.pi * I / N) ^ k)‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ range N, K := Finset.sum_le_sum (fun k _ => hK _ (rootNorm N hN k))
        _ = N * K := by simp
    rw [h1, norm_mul, Complex.norm_natCast] at h2
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    exact le_of_mul_le_mul_left h2 hNpos
  have hlim : Tendsto (fun N : ℕ => ∑ i, y i ^ N / (1 - y i ^ N)) atTop
      (𝓝 (∑ i, if 1 < ‖y i‖ then (-1 : ℂ) else 0)) :=
    tendsto_finsetSum _ (fun i _ => ratioLim (y i) (hy i))
  have hle : ‖∑ i, if 1 < ‖y i‖ then (-1 : ℂ) else 0‖ ≤ K := by
    apply le_of_tendsto hlim.norm
    rw [Filter.eventually_atTop]
    exact ⟨j + 1, fun N hN => hbound N (by omega)⟩
  have hval : ‖∑ i, if 1 < ‖y i‖ then (-1 : ℂ) else 0‖ = ((univ.filter (fun i => 1 < ‖y i‖)).card : ℝ) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, norm_mul, norm_neg,
      norm_one, mul_one, Complex.norm_natCast]
  rw [← hval]
  exact hle

end Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
end
end

section

open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds

def rr (a : ℕ) : ℝ := 16 * Real.exp ((a : ℝ) + 1)
def eps (a : ℕ) : ℝ := 1 / rr a
def th (a : ℕ) : ℝ := 1 / (2 * Real.log (rr a))
def kap (a : ℕ) (D : ℝ) : ℝ := th a * eps a ^ 2 / (a * (D + 1))
def c0 (a : ℕ) : ℝ := 1 / (25 * rr a)
def E0 (a : ℕ) (D : ℝ) : ℝ := Real.exp (a * D / eps a ^ 2)
def j0 (a : ℕ) : ℝ := 1 + a / eps a ^ 2
def GG (a : ℕ) (CP cZ cS c₁ : ℝ) : ℝ :=
  (8 * CP / cZ + 4 / cZ + 32 * CP / cS) * c₁ * Real.exp (j0 a * Real.log (rr a)) + 1 + rr a + rr a ^ 2
def K0 (a : ℕ) (D CP cZ cS c₁ : ℝ) : ℝ := E0 a D * GG a CP cZ cS c₁ / th a

theorem rr_gt (a : ℕ) : 16 < rr a := by
  unfold rr
  have h1 := Real.add_one_le_exp ((a : ℝ) + 1)
  have h2 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  linarith

theorem log_rr_pos (a : ℕ) : 0 < Real.log (rr a) :=
  Real.log_pos (by linarith [rr_gt a])

theorem th_pos (a : ℕ) : 0 < th a := by
  unfold th
  exact div_pos one_pos (mul_pos two_pos (log_rr_pos a))

theorem th_log (a : ℕ) : 2 * th a * Real.log (rr a) = 1 := by
  have hL := (log_rr_pos a).ne'
  unfold th
  have e : 2 * (1 / (2 * Real.log (rr a))) * Real.log (rr a)
      = Real.log (rr a) * (Real.log (rr a))⁻¹ := by ring
  rw [e, mul_inv_cancel₀ hL]

private theorem rr_pos' (a : ℕ) : 0 < rr a := by
  unfold rr
  positivity

theorem eps_pos (a : ℕ) : 0 < eps a := by
  unfold eps
  exact div_pos one_pos (rr_pos' a)

theorem eps_le (a : ℕ) : eps a ≤ 1 / 16 := by
  have h := (rr_gt a).le
  unfold eps
  exact one_div_le_one_div_of_le (by norm_num) h

theorem kap_pos (a : ℕ) (ha : 1 ≤ a) (D : ℝ) (hD : 0 ≤ D) : 0 < kap a D := by
  have ha0 : (0 : ℝ) < a := Nat.cast_pos.mpr (by omega)
  unfold kap
  exact div_pos (mul_pos (th_pos a) (pow_pos (eps_pos a) 2))
    (mul_pos ha0 (by linarith))

private theorem mul_kap_div_eps_sq_eq_th_div_succ (a : ℕ) (ha : 1 ≤ a) (D : ℝ) (hD : 0 ≤ D) :
    (a : ℝ) * kap a D / eps a ^ 2 = th a / (D + 1) := by
  have ha0 : (a : ℝ) ≠ 0 := (Nat.cast_pos.mpr (by omega)).ne'
  have hi : eps a ^ 2 ≠ 0 := (pow_pos (eps_pos a) 2).ne'
  calc (a : ℝ) * kap a D / eps a ^ 2
      = th a / (D + 1) * ((a : ℝ) * (a : ℝ)⁻¹)
          * (eps a ^ 2 * (eps a ^ 2)⁻¹) := by
        have e : ∀ x h i d : ℝ, x * (h * i ^ 2 / (x * d)) / i ^ 2
            = h / d * (x * x⁻¹) * (i ^ 2 * (i ^ 2)⁻¹) := by
          intro x h i d
          ring
        unfold kap
        exact e _ _ _ _
    _ = th a / (D + 1) := by
        rw [mul_inv_cancel₀ ha0, mul_inv_cancel₀ hi, mul_one, mul_one]

private theorem div_mul_cancel_of_ne_zero_real (q d : ℝ) (hd : d ≠ 0) : q / d * d = q := by
  have e : q / d * d = q * (d * d⁻¹) := by ring
  rw [e, mul_inv_cancel₀ hd, mul_one]

theorem akapD_le (a : ℕ) (ha : 1 ≤ a) (D : ℝ) (hD : 0 ≤ D) :
    a * D * kap a D / eps a ^ 2 ≤ th a := by
  have hD1 : (0 : ℝ) < D + 1 := by linarith
  have hq0 : 0 ≤ th a / (D + 1) := (div_pos (th_pos a) hD1).le
  have hq : th a / (D + 1) * (D + 1) = th a :=
    div_mul_cancel_of_ne_zero_real _ _ hD1.ne'
  have e2 : (a : ℝ) * D * kap a D / eps a ^ 2
      = D * ((a : ℝ) * kap a D / eps a ^ 2) := by ring
  rw [e2, mul_kap_div_eps_sq_eq_th_div_succ a ha D hD]
  nlinarith [hq, hq0]

theorem akap_le' (a : ℕ) (ha : 1 ≤ a) (D : ℝ) (hD : 0 ≤ D) : a * kap a D / eps a ^ 2 ≤ th a := by
  have hD1 : (0 : ℝ) < D + 1 := by linarith
  have hq0 : 0 ≤ th a / (D + 1) := (div_pos (th_pos a) hD1).le
  have hq : th a / (D + 1) * (D + 1) = th a :=
    div_mul_cancel_of_ne_zero_real _ _ hD1.ne'
  rw [mul_kap_div_eps_sq_eq_th_div_succ a ha D hD]
  nlinarith [hq, hq0, mul_nonneg hq0 hD]

theorem kap_le (a : ℕ) (ha : 1 ≤ a) (D : ℝ) (hD : 0 ≤ D) : kap a D ≤ th a := by
  have hh := th_pos a
  have hi := eps_pos a
  have hi16 := eps_le a
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hM : (1 : ℝ) ≤ a * (D + 1) := by nlinarith
  have hMne : (a : ℝ) * (D + 1) ≠ 0 := (lt_of_lt_of_le one_pos hM).ne'
  have hs : kap a D * ((a : ℝ) * (D + 1)) = th a * eps a ^ 2 := by
    unfold kap
    exact div_mul_cancel_of_ne_zero_real _ _ hMne
  have hs0 : 0 ≤ kap a D := (kap_pos a ha D hD).le
  have hi2 : eps a ^ 2 ≤ 1 := by
    nlinarith [mul_le_mul hi16 hi16 hi.le (by norm_num : (0 : ℝ) ≤ 1 / 16)]
  have hhi := mul_le_mul_of_nonneg_left hi2 hh.le
  have hsM := mul_le_mul_of_nonneg_left hM hs0
  nlinarith [hs, hhi, hsM]

theorem twentyFive_mul_smallConstant (a : ℕ) : 25 * c0 a = 1 / rr a := by
  unfold c0
  ring

private theorem succ_cube_le_eight_pow (j : ℕ) : (j + 1) ^ 3 ≤ 8 ^ j := by
  induction j with
  | zero => norm_num
  | succ n ih =>
    calc (n + 1 + 1) ^ 3 ≤ (2 * (n + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      _ = 8 * (n + 1) ^ 3 := by ring
      _ ≤ 8 * 8 ^ n := by gcongr
      _ = 8 ^ (n + 1) := by ring

theorem final_step (a : ℕ) (E G : ℝ) (hE : 0 < E) (hG : 0 < G) (j : ℕ)
    (hj : E * G < j)
    (h : 1 / (E * (rr a / 8) ^ j) ≤ G * ((j : ℝ) + 1) ^ 2 / rr a ^ j) : False := by
  have hb := rr_pos' a
  have hP : 0 < (rr a / 8) ^ j := by positivity
  have hB : 0 < rr a ^ j := by positivity
  have hPB : (rr a / 8) ^ j * 8 ^ j = rr a ^ j := by
    rw [← mul_pow]
    congr 1
    ring
  have h1 : 1 / (E * (rr a / 8) ^ j) * (E * (rr a / 8) ^ j) = 1 :=
    div_mul_cancel_of_ne_zero_real _ _ (mul_pos hE hP).ne'
  have h2 : G * ((j : ℝ) + 1) ^ 2 / rr a ^ j * rr a ^ j = G * ((j : ℝ) + 1) ^ 2 :=
    div_mul_cancel_of_ne_zero_real _ _ hB.ne'
  have h3 := mul_le_mul_of_nonneg_right h (mul_pos hE hB).le
  have h4 : (8 : ℝ) ^ j ≤ G * ((j : ℝ) + 1) ^ 2 * E := by
    calc (8 : ℝ) ^ j = 1 / (E * (rr a / 8) ^ j) * (E * (rr a / 8) ^ j) * 8 ^ j := by
          rw [h1, one_mul]
      _ = 1 / (E * (rr a / 8) ^ j) * (E * rr a ^ j) := by
          rw [← hPB]
          ring
      _ ≤ G * ((j : ℝ) + 1) ^ 2 / rr a ^ j * (E * rr a ^ j) := h3
      _ = G * ((j : ℝ) + 1) ^ 2 / rr a ^ j * rr a ^ j * E := by ring
      _ = G * ((j : ℝ) + 1) ^ 2 * E := by rw [h2]
  have hc : ((j : ℝ) + 1) ^ 3 ≤ 8 ^ j := by exact_mod_cast succ_cube_le_eight_pow j
  have hm := mul_lt_mul_of_pos_right hj (by positivity : (0 : ℝ) < ((j : ℝ) + 1) ^ 2)
  nlinarith [hm, hc, h4, sq_nonneg ((j : ℝ) + 1)]

end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
end
end

section

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts

def ZeroDensityBox : Prop :=
  ∃ C : ℝ, ∀ (Q : ℝ) (S : Finset (Σ N : ℕ, DirichletCharacter ℂ (N + 1))), 3 ≤ Q →
    (∀ p ∈ S, p.2.IsPrimitive ∧ ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧
      ∃ s : ℂ, 1 - 1 / 400 < s.re ∧ |s.im| ≤ Q ∧ DirichletCharacter.LFunction p.2 s = 0) →
    (S.card : ℝ) ≤ C * Q ^ (1 / 4 : ℝ)

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts
end
end
