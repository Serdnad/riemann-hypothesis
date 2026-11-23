module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.Bundle001
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.Bundle002
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem landau_pole_asym_deriv (c ρ z : ℂ) (k : ℕ) :
    iteratedDeriv k (fun s : ℂ => c * (s - ρ)⁻¹) z
      = c * ((-1) ^ k * (k.factorial : ℂ) * ((z - ρ) ^ (k + 1))⁻¹) := by
  rw [iteratedDeriv_const_mul_field]
  congr 1
  have e := congrFun (iteratedDeriv_comp_sub_const k (fun t : ℂ => t⁻¹) ρ) z
  rw [e, iteratedDeriv_eq_iterate, show (fun t : ℂ => t⁻¹) = Inv.inv from rfl, iter_deriv_inv,
    show (-1 - k : ℤ) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]

theorem landau_pole_asym {Φ : ℂ → ℂ} {z ρ c : ℂ} {r r' : ℝ} (hρ : ρ ∈ Metric.ball z r) (hne : ρ ≠ z)
    (hd : DifferentiableOn ℂ Φ (Metric.ball z r \ {ρ}))
    (hp : ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧ ∀ᶠ s in 𝓝[≠] ρ, Φ s = c / (s - ρ) + h s)
    (h0 : 0 < r') (h1 : r' < r) :
    ∃ M : ℝ, ∀ k : ℕ,
      ‖(-1) ^ k * iteratedDeriv k Φ z / (k.factorial : ℂ) - c / (z - ρ) ^ (k + 1)‖ ≤ M / r' ^ k := by
  obtain ⟨hfun, han, hev⟩ := hp
  have hopen : IsOpen (Metric.ball z r \ {ρ}) := Metric.isOpen_ball.sdiff isClosed_singleton
  set G : ℂ → ℂ := fun s => if s = ρ then hfun ρ else Φ s - c / (s - ρ) with hG
  have hGeq : G =ᶠ[𝓝 ρ] hfun := by
    rw [eventually_nhdsWithin_iff] at hev
    filter_upwards [hev] with s hs
    by_cases hsρ : s = ρ
    · rw [hsρ]
      simp [G]
    · simp only [G, if_neg hsρ]
      rw [hs (Set.mem_compl_singleton_iff.mpr hsρ)]
      ring
  have hGd : DifferentiableOn ℂ G (Metric.ball z r) := by
    intro s hs
    by_cases hsρ : s = ρ
    · rw [hsρ]
      exact ((hGeq.differentiableAt_iff).mpr han.differentiableAt).differentiableWithinAt
    · have hmem : s ∈ Metric.ball z r \ {ρ} := ⟨hs, hsρ⟩
      have hΦ : DifferentiableAt ℂ Φ s := (hd s hmem).differentiableAt (hopen.mem_nhds hmem)
      have hloc : G =ᶠ[𝓝 s] fun t => Φ t - c / (t - ρ) := by
        filter_upwards [hopen.mem_nhds hmem] with t ht
        have htρ : t ≠ ρ := ht.2
        simp only [G, if_neg htρ]
      have hd' : DifferentiableAt ℂ (fun t => Φ t - c / (t - ρ)) s :=
        hΦ.sub ((differentiableAt_const c).div
          (differentiableAt_id.sub (differentiableAt_const ρ)) (sub_ne_zero.mpr hsρ))
      exact ((hloc.differentiableAt_iff).mpr hd').differentiableWithinAt
  obtain ⟨M, hM⟩ := landau_cauchy hGd h0 h1
  refine ⟨M, fun k => ?_⟩
  have hzρ : z ≠ ρ := Ne.symm hne
  have hr : 0 < r := lt_trans h0 h1
  have hmemz : z ∈ Metric.ball z r \ {ρ} := ⟨Metric.mem_ball_self hr, hzρ⟩
  have hloc : Φ =ᶠ[𝓝 z] G + fun s => c * (s - ρ)⁻¹ := by
    filter_upwards [hopen.mem_nhds hmemz] with t ht
    have htρ : t ≠ ρ := ht.2
    simp only [Pi.add_apply, G, if_neg htρ, div_eq_mul_inv]
    ring
  have hGc : ContDiffAt ℂ k G z :=
    (hGd.contDiffOn Metric.isOpen_ball).contDiffAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
  have hPc : ContDiffAt ℂ k (fun s => c * (s - ρ)⁻¹) z := by
    have hs : ContDiffAt ℂ k (fun s : ℂ => s - ρ) z := contDiffAt_id.sub contDiffAt_const
    exact contDiffAt_const.mul (hs.inv (sub_ne_zero.mpr hzρ))
  rw [hloc.iteratedDeriv_eq, iteratedDeriv_add hGc hPc, landau_pole_asym_deriv]
  have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hpow : ((-1 : ℂ)) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  set iG := iteratedDeriv k G z
  set X := (z - ρ) ^ (k + 1)
  have e : (-1) ^ k * (iG + c * ((-1) ^ k * (k.factorial : ℂ) * X⁻¹)) / (k.factorial : ℂ) - c / X
      = (-1) ^ k * (iG / k.factorial) := by
    calc _ = (-1) ^ k * (iG / k.factorial) + ((-1) ^ k * (-1) ^ k) * c *
          ((k.factorial : ℂ) / k.factorial) * X⁻¹ - c / X := by ring
      _ = _ := by rw [hpow, div_self hfac, div_eq_mul_inv c]; ring
  rw [e, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact hM k

end Deduction

end
end

section

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

lemma landau_tails_integrable (k : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => u ^ k * Real.exp (-a * u) / (k.factorial : ℝ)) (Ioi 0) := by
  by_contra h
  have h1 := kernel_integral k a ha
  rw [integral_undef h] at h1
  have : 0 < (a ^ (k + 1))⁻¹ := by positivity
  linarith

lemma landau_tails_chernoff (k : ℕ) {s l U V : ℝ} (hl : 0 ≤ l) (hs : l < s) :
    ∫ u in Ioi (0 : ℝ) \ Icc U V, u ^ k * Real.exp (-s * u) / (k.factorial : ℝ) ≤
      Real.exp (-(l * V)) * ((s - l) ^ (k + 1))⁻¹ + Real.exp (l * U) * ((s + l) ^ (k + 1))⁻¹ := by
  have ha : 0 < s - l := by linarith
  have hb : 0 < s + l := by linarith
  have hs0 : 0 < s := by linarith
  have i1 := (landau_tails_integrable k ha).const_mul (Real.exp (-(l * V)))
  have i2 := (landau_tails_integrable k hb).const_mul (Real.exp (l * U))
  have i0 := landau_tails_integrable k hs0
  have i3 := i1.add i2
  rw [← kernel_integral k _ ha, ← kernel_integral k _ hb, ← integral_const_mul, ← integral_const_mul,
    ← integral_add i1 i2]
  have hm : MeasurableSet (Ioi (0 : ℝ) \ Icc U V) := measurableSet_Ioi.diff measurableSet_Icc
  refine le_trans (setIntegral_mono_on (IntegrableOn.mono_set i0 sdiff_subset)
    (IntegrableOn.mono_set i3 sdiff_subset) hm ?_)
    (setIntegral_mono_set i3 ?_ (Filter.Eventually.of_forall fun _ h => h.1))
  · intro u hu
    have hu0 : 0 < u := hu.1
    have hf : 0 < (k.factorial : ℝ) := by positivity
    have hp : 0 ≤ u ^ k / (k.factorial : ℝ) := by positivity
    have e1 : Real.exp (-(l * V)) * Real.exp (-(s - l) * u) = Real.exp (-s * u + l * (u - V)) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (l * U) * Real.exp (-(s + l) * u) = Real.exp (-s * u + l * (U - u)) := by
      rw [← Real.exp_add]; congr 1; ring
    have key : Real.exp (-s * u) ≤ Real.exp (-s * u + l * (u - V)) + Real.exp (-s * u + l * (U - u)) := by
      have hn := hu.2
      rw [mem_Icc, not_and_or, not_le, not_le] at hn
      rcases hn with h | h
      · have : Real.exp (-s * u) ≤ Real.exp (-s * u + l * (U - u)) :=
          Real.exp_le_exp.2 (by nlinarith [mul_nonneg hl (sub_nonneg.2 h.le)])
        linarith [Real.exp_pos (-s * u + l * (u - V))]
      · have : Real.exp (-s * u) ≤ Real.exp (-s * u + l * (u - V)) :=
          Real.exp_le_exp.2 (by nlinarith [mul_nonneg hl (sub_nonneg.2 h.le)])
        linarith [Real.exp_pos (-s * u + l * (U - u))]
    rw [← e1, ← e2] at key
    have := mul_le_mul_of_nonneg_left key hp
    simp only [Pi.add_apply]
    calc _ = u ^ k / (k.factorial : ℝ) * Real.exp (-s * u) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := hu
    simp only [Pi.add_apply, Pi.zero_apply]
    positivity

lemma landau_tails_pow (k : ℕ) {σ a x c : ℝ} (hσ : 0 < σ) (ha : 0 < a)
    (h : x + k * ((σ - a) / a) ≤ c) :
    Real.exp x * (a ^ (k + 1))⁻¹ ≤ Real.exp c / a / σ ^ k := by
  have h1 : σ / a ≤ Real.exp ((σ - a) / a) := by
    have := Real.add_one_le_exp ((σ - a) / a)
    have e : (σ - a) / a + 1 = σ / a := by field_simp; ring
    linarith
  have h2 : (σ / a) ^ k ≤ Real.exp (k * ((σ - a) / a)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) h1 k
  have h3 : Real.exp x * (σ / a) ^ k ≤ Real.exp c := by
    calc _ ≤ Real.exp x * Real.exp (k * ((σ - a) / a)) := by gcongr
      _ = Real.exp (x + k * ((σ - a) / a)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.2 h
  calc _ = Real.exp x * (σ / a) ^ k / a / σ ^ k := by
        rw [div_pow, pow_succ]; field_simp
    _ ≤ _ := by gcongr

theorem landau_tails {δ : ℝ} (hδ : 0 < δ) :
    ∃ σ : ℝ, 2 < σ ∧ ∃ C : ℝ, ∀ U : ℝ, 1 ≤ U → ∃ k : ℕ, U ≤ k ∧
      ∫ u in Ioi (0 : ℝ) \ Icc U ((1 + δ) * U), u ^ k * Real.exp ((2 - σ) * u) / (k.factorial : ℝ) ≤ C / σ ^ k := by
  obtain ⟨l, hl2, hl⟩ : ∃ l : ℝ, 2 < l ∧ l * δ = 6 + 2 * δ := by
    refine ⟨2 + 6 / δ, by have : 0 < 6 / δ := by positivity
                          linarith, by field_simp; ring⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = l * (1 + δ) := ⟨_, rfl⟩
  have hMl : l < M := by nlinarith
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = M * (2 + l) := ⟨_, rfl⟩
  have hσ1 : l * (2 + l) < σ := by rw [hσ]; gcongr
  have hs : l < σ - 2 := by nlinarith
  have ha : 0 < σ - 2 - l := by linarith
  have hb : 0 < σ - 2 + l := by linarith
  have hσ0 : 0 < σ := by linarith
  refine ⟨σ, by linarith, Real.exp 1 / (σ - 2 - l) + Real.exp 0 / (σ - 2 + l), fun U hU => ?_⟩
  have hx : 0 ≤ (1 + δ / 2) * σ * U := by positivity
  have hk1 := Nat.le_ceil ((1 + δ / 2) * σ * U)
  have hk2 := (Nat.ceil_lt_add_one hx).le
  set k := ⌈(1 + δ / 2) * σ * U⌉₊
  have hσU : 0 ≤ σ * U := by positivity
  refine ⟨k, ?_, ?_⟩
  · nlinarith [mul_nonneg hδ.le hσU]
  · have e : (2 - σ) = -(σ - 2) := by ring
    rw [e, add_div]
    refine (landau_tails_chernoff k (by linarith : 0 ≤ l) hs).trans (add_le_add ?_ ?_)
    · apply landau_tails_pow k hσ0 ha
      have e1 : (σ - (σ - 2 - l)) / (σ - 2 - l) = 1 / (M - 1) := by
        have : 0 < M - 1 := by linarith
        rw [div_eq_div_iff ha.ne' this.ne', hσ]; ring
      have e2 : (1 + δ / 2) * σ = M * (M - 1) := by
        have : (1 + δ / 2) * (2 + l) = M - 1 := by rw [hM]; nlinarith
        rw [hσ, ← this]; ring
      have hM1 : 1 ≤ M - 1 := by linarith
      have e3 : (k : ℝ) * (1 / (M - 1)) ≤ M * U + 1 := by
        rw [mul_one_div, div_le_iff₀ (by linarith)]
        rw [e2] at hk2
        nlinarith
      have e4 : l * ((1 + δ) * U) = M * U := by rw [hM]; ring
      rw [e1, e4]; linarith
    · apply landau_tails_pow k hσ0 hb
      have e1 : (k : ℝ) * ((σ - (σ - 2 + l)) / (σ - 2 + l)) = -((k : ℝ) * (l - 2) / (σ - 2 + l)) := by
        ring
      have e2 : (1 + δ / 2) * (l - 2) = l + 1 := by nlinarith
      have e3 : l * U ≤ (k : ℝ) * (l - 2) / (σ - 2 + l) := by
        rw [le_div_iff₀ hb]
        have h1 : (1 + δ / 2) * σ * U * (l - 2) ≤ k * (l - 2) :=
          mul_le_mul_of_nonneg_right hk1 (by linarith)
        have h2 : (1 + δ / 2) * σ * U * (l - 2) = (l + 1) * σ * U := by rw [← e2]; ring
        have h3 : l * (σ - 2 + l) ≤ (l + 1) * σ := by nlinarith
        have h4 := mul_le_mul_of_nonneg_right h3 (by linarith : 0 ≤ U)
        nlinarith
      rw [e1]; linarith

end Deduction

end
end
