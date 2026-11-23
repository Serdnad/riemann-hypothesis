module

public import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion
public import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem landau_pole_re_le_bound {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z) {σ : ℝ}
    (hσ : 2 < σ) : ∃ M : ℝ, ∀ s : ℂ, σ ≤ s.re → ‖Φ s‖ ≤ M := by
  obtain ⟨C, hC⟩ := hP.growth
  refine ⟨∫ u in Ioi (0 : ℝ), C * Real.exp (-(σ - 2) * u), fun s hs => ?_⟩
  rw [hP.laplace s (lt_of_lt_of_le hσ hs)]
  refine norm_integral_le_of_norm_le
    ((exp_neg_integrableOn_Ioi 0 (sub_pos.mpr hσ)).const_mul C) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := le_of_lt hu
  have h1 := hC u hu0
  have hre : (-s * (u : ℂ)).re = -s.re * u := by simp
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, hre]
  have h2 : Real.exp (-s.re * u) ≤ Real.exp (-σ * u) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc |g u| * Real.exp (-s.re * u) ≤ (C * Real.exp (2 * u)) * Real.exp (-σ * u) :=
        mul_le_mul h1 h2 (Real.exp_pos _).le ((abs_nonneg _).trans h1)
    _ = C * Real.exp (-(σ - 2) * u) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem landau_pole_re_le {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z) : ∀ ρ ∈ Z, ρ.re ≤ 2 := by
  intro ρ hρ
  by_contra hlt
  have hlt : 2 < ρ.re := not_le.mp hlt
  obtain ⟨M, hM⟩ := landau_pole_re_le_bound hP (σ := (2 + ρ.re) / 2) (by linarith)
  obtain ⟨c, hc, -, h, hh, hev⟩ := hP.pole ρ hρ
  have h0 : Tendsto (fun s : ℂ => s - ρ) (𝓝[≠] ρ) (𝓝 0) := by
    have : Tendsto (fun s : ℂ => s - ρ) (𝓝 ρ) (𝓝 (ρ - ρ)) := tendsto_id.sub_const ρ
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hb : ∀ᶠ s in 𝓝[≠] ρ, ‖Φ s‖ ≤ M := by
    have : ∀ᶠ s in 𝓝 ρ, (2 + ρ.re) / 2 < s.re :=
      Complex.continuous_re.continuousAt.eventually (lt_mem_nhds (by linarith))
    filter_upwards [this.filter_mono nhdsWithin_le_nhds] with s hs using hM s hs.le
  have h1 : Tendsto (fun s : ℂ => (s - ρ) * Φ s) (𝓝[≠] ρ) (𝓝 0) :=
    NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded h0 ⟨M, eventually_map.mpr hb⟩
  have h2 : Tendsto (fun s : ℂ => c + (s - ρ) * h s) (𝓝[≠] ρ) (𝓝 (c + 0 * h ρ)) :=
    (h0.mul (hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)).const_add c
  have h3 : (fun s : ℂ => (s - ρ) * Φ s) =ᶠ[𝓝[≠] ρ] fun s : ℂ => c + (s - ρ) * h s := by
    filter_upwards [hev, self_mem_nhdsWithin] with s hs hne
    have : s - ρ ≠ 0 := sub_ne_zero.mpr hne
    rw [hs]; field_simp
  have := tendsto_nhds_unique (h1.congr' h3) h2
  apply hc
  simpa using this.symm

end Deduction

end
end

section

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem windowHypU_of_windowHyp_image (a b : ℝ) :
    Real.exp '' Icc a b = Icc (Real.exp a) (Real.exp b) := by
  ext y
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨Real.exp_le_exp.2 h1, Real.exp_le_exp.2 h2⟩
  · rintro ⟨h1, h2⟩
    have hy : 0 < y := lt_of_lt_of_le (Real.exp_pos a) h1
    refine ⟨Real.log y, ⟨?_, ?_⟩, Real.exp_log hy⟩
    · rw [← Real.exp_le_exp, Real.exp_log hy]; exact h1
    · rw [← Real.exp_le_exp, Real.exp_log hy]; exact h2

theorem windowHypU_of_windowHyp_fun (R : ℝ → ℝ) (θ : ℝ) :
    (fun u : ℝ => |Real.exp u| • (R (Real.exp u) * Real.exp u ^ (-θ - 1))) =
      fun u => R (Real.exp u) * Real.exp (-θ * u) := by
  funext u
  rw [abs_of_pos (Real.exp_pos u), smul_eq_mul, ← Real.exp_mul, mul_left_comm, ← Real.exp_add]
  congr 2
  ring

theorem windowHypU_of_windowHyp (F : CharFamily) {θ δ : ℝ} (hδ : 0 < δ) (h : WindowHyp F θ δ) :
    WindowHypU (gm F) θ δ := by
  intro η hη U₀
  obtain ⟨Y, hY, R, hint, hR, hbound⟩ := h η hη (Real.exp U₀)
  have hYpos : 0 < Y := lt_of_lt_of_le (Real.exp_pos _) hY
  have hS : Real.exp '' Icc (Real.log Y) ((1 + δ) * Real.log Y) = Icc Y (Y ^ (1 + δ)) := by
    rw [windowHypU_of_windowHyp_image, Real.exp_log hYpos, Real.rpow_def_of_pos hYpos, mul_comm]
  have hd : ∀ x ∈ Icc (Real.log Y) ((1 + δ) * Real.log Y),
      HasDerivWithinAt Real.exp (Real.exp x) (Icc (Real.log Y) ((1 + δ) * Real.log Y)) x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hinj : InjOn Real.exp (Icc (Real.log Y) ((1 + δ) * Real.log Y)) :=
    Real.exp_injective.injOn
  refine ⟨Real.log Y, ?_, fun u => R (Real.exp u), ?_, ?_, ?_⟩
  · rw [← Real.exp_le_exp, Real.exp_log hYpos]; exact hY
  · have := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Icc hd hinj
      (fun y => R y * y ^ (-θ - 1))).1 (by rw [hS]; exact hint)
    rw [windowHypU_of_windowHyp_fun] at this
    exact this
  · intro u hu
    have hmem : Real.exp u ∈ Icc Y (Y ^ (1 + δ)) := by
      rw [← hS]; exact ⟨u, hu, rfl⟩
    exact hR _ hmem
  · have e := integral_image_eq_integral_abs_deriv_smul measurableSet_Icc hd hinj
      (fun y => R y * y ^ (-θ - 1))
    rw [hS, windowHypU_of_windowHyp_fun] at e
    rw [← e]
    calc ∫ y in Icc Y (Y ^ (1 + δ)), R y * y ^ (-θ - 1) ≤ Y ^ η := hbound
      _ = Real.exp (η * Real.log Y) := by rw [Real.rpow_def_of_pos hYpos, mul_comm]

end Deduction

end
end

section

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem landau_coeff {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z) (k : ℕ) {s : ℂ} (hs : 2 < s.re) :
    (-1) ^ k * iteratedDeriv k Φ s / (k.factorial : ℂ) =
      ∫ u in Ioi (0 : ℝ), (g u : ℂ) * (u : ℂ) ^ k * cexp (-s * u) / (k.factorial : ℂ) := by
  obtain ⟨C, hC⟩ := hP.growth
  have hev : Φ =ᶠ[𝓝 s] (fun z => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-z * u)) := by
    have hopen : IsOpen {z : ℂ | 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact hP.laplace z hz
  rw [hev.iteratedDeriv_eq k, iteratedDeriv_laplace g hP.meas C hC k s hs, ← integral_const_mul,
    ← integral_div]
  congr 1
  funext u
  push_cast
  have e : ((-1 : ℂ)) ^ k * (-(u : ℂ)) ^ k = (u : ℂ) ^ k := by
    rw [← mul_pow]
    ring
  calc (-1 : ℂ) ^ k * ((g u : ℂ) * (-(u : ℂ)) ^ k * cexp (-s * u)) / (k.factorial : ℂ)
      = (g u : ℂ) * ((-1 : ℂ) ^ k * (-(u : ℂ)) ^ k) * cexp (-s * u) / (k.factorial : ℂ) := by ring
    _ = (g u : ℂ) * (u : ℂ) ^ k * cexp (-s * u) / (k.factorial : ℂ) := by rw [e]

end Deduction

end
end
