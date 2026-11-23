module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle002
public import Mathlib.NumberTheory.LSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle005
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle010
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableOddTheta
public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle011
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Aesop.Main
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle012
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
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.Linearity
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk

theorem tsum_prod_weight_approx {ι κ : Type} (u : ι → κ → ℝ) (w : κ → ℝ) (A a C c : ℝ) (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hu0 : ∀ m k, 0 ≤ u m k) (hw0 : ∀ k, 0 ≤ w k)
    (hu : ∀ k, Summable (fun m => u m k) ∧ |∑' m, u m k - A| ≤ A * a)
    (hw : Summable w ∧ |∑' k, w k - C| ≤ C * c) :
    Summable (fun v : ι × κ => u v.1 v.2 * w v.2) ∧
      |∑' v : ι × κ, u v.1 v.2 * w v.2 - A * C| ≤ A * C * (a + c + a * c) := by
  have hin : ∀ k, ∑' m, u m k * w k = (∑' m, u m k) * w k := fun k => tsum_mul_right
  have hb : ∀ k, ‖(∑' m, u m k - A) * w k‖ ≤ A * a * w k := fun k => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 k)]
    exact mul_le_mul_of_nonneg_right (hu k).2 (hw0 k)
  have hs1 : Summable (fun k => (∑' m, u m k - A) * w k) :=
    Summable.of_norm_bounded (hw.1.mul_left (A * a)) hb
  have hs2 : Summable (fun k => (∑' m, u m k) * w k) := by
    refine (hs1.add (hw.1.mul_left A)).congr fun k => ?_
    ring
  have hsw : Summable (fun v : κ × ι => u v.2 v.1 * w v.1) := by
    rw [summable_prod_of_nonneg (fun v => mul_nonneg (hu0 _ _) (hw0 _))]
    refine ⟨fun k => ?_, ?_⟩
    · exact (hu k).1.mul_right (w k)
    · exact hs2.congr fun k => (hin k).symm
  have hs : Summable (fun v : ι × κ => u v.1 v.2 * w v.2) :=
    hsw.prod_symm
  refine ⟨hs, ?_⟩
  have h1 : ∑' v : ι × κ, u v.1 v.2 * w v.2 = ∑' k, (∑' m, u m k) * w k := by
    rw [← (Equiv.prodComm κ ι).tsum_eq]
    have := hsw.tsum_prod
    simp only [hin] at this
    exact this
  have h2 : ∑' k, (∑' m, u m k) * w k = ∑' k, (∑' m, u m k - A) * w k + A * ∑' k, w k := by
    rw [← tsum_mul_left, ← hs1.tsum_add (hw.1.mul_left A)]
    exact tsum_congr fun k => by ring
  have h3 : |∑' k, (∑' m, u m k - A) * w k| ≤ A * a * ∑' k, w k := by
    have := tsum_of_norm_bounded (hw.1.hasSum.mul_left (A * a)) hb
    simpa using this
  rw [h1, h2]
  have h4 := abs_le.mp hw.2
  have h5 := abs_le.mp h3
  have h6 : A * a * ∑' k, w k ≤ A * a * (C + C * c) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hA ha)
  have h7 : A * (∑' k, w k - C) ≤ A * (C * c) := mul_le_mul_of_nonneg_left h4.2 hA
  have h8 : A * (-(C * c)) ≤ A * (∑' k, w k - C) := mul_le_mul_of_nonneg_left h4.1 hA
  rw [abs_le]
  constructor <;> nlinarith

theorem theta_qForm : ∀ α γ l θ₁ θ₂ t : ℝ, 0 < α → 0 < γ → 0 < t → Summable (fun v : ℤ × ℤ => Real.exp (-(t * qForm α γ l θ₁ θ₂ v))) ∧ |∑' v : ℤ × ℤ, Real.exp (-(t * qForm α γ l θ₁ θ₂ v)) - Real.pi / Real.sqrt (α * γ) / t| ≤ Real.pi / Real.sqrt (α * γ) / t * ((α * t) ^ 2 + (γ * t) ^ 2 + (α * t) ^ 2 * (γ * t) ^ 2) := by
  intro α γ l θ₁ θ₂ t hα hγ ht
  have h := tsum_prod_weight_approx
    (fun (m : ℤ) (k : ℤ) => Real.exp (-((α * t) * (m + (θ₁ + l * k)) ^ 2)))
    (fun k : ℤ => Real.exp (-((γ * t) * (k + θ₂) ^ 2)))
    (Real.sqrt (Real.pi / (α * t))) ((α * t) ^ 2) (Real.sqrt (Real.pi / (γ * t))) ((γ * t) ^ 2)
    (Real.sqrt_nonneg _) (sq_nonneg _) (fun _ _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
    (fun k => GlobalTheory.ShiftedTheta.shifted_theta_bound (α * t) (θ₁ + l * k) (mul_pos hα ht))
    (GlobalTheory.ShiftedTheta.shifted_theta_bound (γ * t) θ₂ (mul_pos hγ ht))
  have e1 : (fun v : ℤ × ℤ => Real.exp (-(t * qForm α γ l θ₁ θ₂ v))) =
      fun v : ℤ × ℤ => Real.exp (-((α * t) * (v.1 + (θ₁ + l * v.2)) ^ 2)) *
        Real.exp (-((γ * t) * (v.2 + θ₂) ^ 2)) := by
    funext v
    rw [← Real.exp_add]
    congr 1
    unfold qForm
    ring
  have e2 : Real.pi / Real.sqrt (α * γ) / t =
      Real.sqrt (Real.pi / (α * t)) * Real.sqrt (Real.pi / (γ * t)) := by
    have hp := Real.pi_pos
    rw [← Real.sqrt_mul (by positivity)]
    symm
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
    have hs : Real.sqrt (α * γ) * Real.sqrt (α * γ) = α * γ := Real.mul_self_sqrt (by positivity)
    have hs0 : 0 < Real.sqrt (α * γ) := Real.sqrt_pos.mpr (by positivity)
    rw [div_div, div_mul_div_comm, div_mul_div_comm]
    congr 1
    linear_combination -t ^ 2 * hs
  rw [e1, e2]
  exact h

end GlobalTheory.Hk
end

section

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk.LFamPos

theorem norm_lamChi_le (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (n : ℕ) : ‖𝓕.lamChi χ n‖ ≤ 2 * Λ n := by
  refine le_trans ?_ (𝓕.lam_le n)
  unfold LFam.lamChi
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun g _ => ?_)
  rw [norm_mul, AddChar.norm_apply, one_mul, Complex.norm_real, Real.norm_of_nonneg (𝓕.lam_nonneg g n)]

theorem summable_lamChi (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (𝓕.lamChi χ) s := by
  have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).smul (2 : ℂ)
  refine Summable.of_norm_bounded h.norm fun n => ?_
  refine LSeries.norm_term_le s ?_
  refine (norm_lamChi_le 𝓕 χ n).trans (le_of_eq ?_)
  simp [abs_of_nonneg vonMangoldt_nonneg]

theorem hasSum_re (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (σ : ℝ) (u : ℂ) (hs : 1 < σ) (hu : u.re = 0) :
    HasSum (fun n : ℕ => ∑ g, (if n = 0 then 0 else 𝓕.lam g n * (n : ℝ) ^ (-σ)) * (χ g * (n : ℂ) ^ (-u)).re)
      (LSeries (𝓕.lamChi χ) (σ + u)).re := by
  have h := (summable_lamChi 𝓕 χ (s := σ + u) (by simpa [hu] using hs)).hasSum
  have h2 := Complex.hasSum_re h
  convert h2 using 2 with n
  · by_cases hn : n = 0
    · simp [hn]
    · have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      rw [LSeries.term_of_ne_zero hn, LFam.lamChi, Finset.sum_div, Complex.re_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [if_neg hn, ← Complex.re_ofReal_mul]
      congr 1
      rw [div_eq_mul_inv, ← cpow_neg, neg_add, cpow_add _ _ hn']
      push_cast
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
      push_cast
      ring
  · rfl

theorem hasSum_re₀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (σ : ℝ) (hs : 1 < σ) :
    HasSum (fun n : ℕ => ∑ g, (if n = 0 then 0 else 𝓕.lam g n * (n : ℝ) ^ (-σ)) * (χ g).re)
      (LSeries (𝓕.lamChi χ) σ).re := by
  simpa using hasSum_re 𝓕 χ σ 0 hs rfl

theorem w_nonneg (𝓕 : LFam) (σ : ℝ) (n : ℕ) (g : 𝓕.G) :
    0 ≤ (if n = 0 then 0 else 𝓕.lam g n * (n : ℝ) ^ (-σ)) := by
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (𝓕.lam_nonneg g n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem pm_one {G : Type} [AddCommGroup G] (χ : AddChar G ℂ) (h : χ * χ = 1) (g : G) :
    χ g = 1 ∨ χ g = -1 := by
  have : χ g * χ g = 1 := by
    have := congrArg (fun φ : AddChar G ℂ => φ g) h
    simpa using this
  exact mul_self_eq_one_iff.mp this

theorem trig (z : ℂ) (hz : ‖z‖ = 1) : 0 ≤ 3 + 4 * z.re + (z * z).re := by
  have h : z.re * z.re + z.im * z.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hz]; norm_num
  rw [Complex.mul_re]
  nlinarith [sq_nonneg (z.re + 1)]

theorem positivity : ∀ (𝓕 : LFam) (χ ψ : AddChar 𝓕.G ℂ) (σ t : ℝ), 1 < σ → 0 ≤ 3 * (LSeries (𝓕.lamChi 1) σ).re + 4 * (LSeries (𝓕.lamChi χ) (σ + t * I)).re + (LSeries (𝓕.lamChi (χ * χ)) (σ + 2 * t * I)).re ∧ 0 ≤ (LSeries (𝓕.lamChi 1) σ).re ∧ (χ * χ = 1 → ψ * ψ = 1 → 0 ≤ (LSeries (𝓕.lamChi 1) σ).re + (LSeries (𝓕.lamChi χ) σ).re ∧ 0 ≤ (LSeries (𝓕.lamChi 1) σ).re + (LSeries (𝓕.lamChi χ) σ).re + (LSeries (𝓕.lamChi ψ) σ).re + (LSeries (𝓕.lamChi (χ * ψ)) σ).re) := by
  intro 𝓕 χ ψ σ t hσ
  have h1 := hasSum_re₀ 𝓕 1 σ hσ
  refine ⟨?_, ?_, fun hχ hψ => ⟨?_, ?_⟩⟩
  · have h2 := hasSum_re 𝓕 χ σ (t * I) hσ (by simp)
    have h3 := hasSum_re 𝓕 (χ * χ) σ (2 * t * I) hσ (by simp)
    refine HasSum.nonneg (fun n => ?_) (((h1.mul_left 3).add (h2.mul_left 4)).add h3)
    by_cases hn : n = 0
    · simp [hn]
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_nonneg fun g _ => ?_
    have hz : ‖χ g * (n : ℂ) ^ (-(t * I))‖ = 1 := by
      rw [norm_mul, AddChar.norm_apply, one_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      simp
    have ht := trig _ hz
    have he : (χ * χ) g * (n : ℂ) ^ (-(2 * t * I)) = (χ g * (n : ℂ) ^ (-(t * I))) * (χ g * (n : ℂ) ^ (-(t * I))) := by
      rw [show -(2 * (t : ℂ) * I) = -(t * I) + -(t * I) by ring, cpow_add _ _ hn', AddChar.mul_apply]
      ring
    rw [he, AddChar.one_apply, Complex.one_re]
    have := mul_nonneg (w_nonneg 𝓕 σ n g) ht
    linarith
  · refine HasSum.nonneg (fun n => Finset.sum_nonneg fun g _ => ?_) h1
    rw [AddChar.one_apply, Complex.one_re, mul_one]
    exact w_nonneg 𝓕 σ n g
  · refine HasSum.nonneg (fun n => ?_) (h1.add (hasSum_re₀ 𝓕 χ σ hσ))
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_nonneg fun g _ => ?_
    have hw := w_nonneg 𝓕 σ n g
    rw [AddChar.one_apply]
    rcases pm_one χ hχ g with h | h <;> rw [h] <;> simp only [one_re, neg_re] <;> linarith
  · refine HasSum.nonneg (fun n => ?_) (((h1.add (hasSum_re₀ 𝓕 χ σ hσ)).add (hasSum_re₀ 𝓕 ψ σ hσ)).add (hasSum_re₀ 𝓕 (χ * ψ) σ hσ))
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_nonneg fun g _ => ?_
    have hw := w_nonneg 𝓕 σ n g
    rw [AddChar.one_apply, AddChar.mul_apply]
    rcases pm_one χ hχ g with h | h <;> rcases pm_one ψ hψ g with h' | h' <;> rw [h, h'] <;>
      simp only [one_re, neg_re, mul_one, mul_neg, neg_neg] <;> linarith

end GlobalTheory.Hk.LFamPos
end

section

open MeasureTheory Topology

theorem _root_.GlobalTheory.T.exists_compact_open_units_subgroup_continuous_sqrt : ∀ (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K], (2 : K) ≠ 0 → ∃ (U : Set K) (s : K → K), GlobalTheory.QuadFibre.IsSqrtOn U s := by
  first | exact @GlobalTheory.QuadFibre.exists_isSqrtOn | exact GlobalTheory.QuadFibre.exists_isSqrtOn | (intros; apply GlobalTheory.QuadFibre.exists_isSqrtOn <;> assumption)
end

section

open Complex
open scoped Real

namespace GlobalTheory.JacobiTriple.QBinomial

open GlobalTheory.JacobiTriple

theorem qPoch_succ (t : ℂ) (n : ℕ) : qPoch t (n + 1) = qPoch t n * (1 - t ^ (n + 1)) := by
  unfold qPoch; rw [Finset.prod_range_succ]

theorem qBinom_zero_right (t : ℂ) (ht : ‖t‖ < 1) (m : ℕ) : qBinom t m 0 = 1 := by
  have h := (qPoch_tendsto t ht).2.2 m
  unfold qBinom; rw [show qPoch t 0 = 1 by simp [qPoch], Nat.sub_zero]; field_simp

theorem qBinom_self (t : ℂ) (ht : ‖t‖ < 1) (m : ℕ) : qBinom t m m = 1 := by
  have h := (qPoch_tendsto t ht).2.2 m
  unfold qBinom; simp [Nat.sub_self]; rw [show qPoch t 0 = 1 by simp [qPoch]]; field_simp

theorem qBinom_pascal (t : ℂ) (ht : ‖t‖ < 1) (m k : ℕ) (hk : k < m) :
    qBinom t (m + 1) (k + 1) = qBinom t m (k + 1) + t ^ (m - k) * qBinom t m k := by
  obtain ⟨j, rfl⟩ : ∃ j, m = k + 1 + j := ⟨m - (k + 1), by omega⟩
  have hne := (qPoch_tendsto t ht).2.2
  have e1 : k + 1 + j + 1 - (k + 1) = j + 1 := by omega
  have e2 : k + 1 + j - (k + 1) = j := by omega
  have e3 : k + 1 + j - k = j + 1 := by omega
  unfold qBinom
  rw [e1, e2, e3, qPoch_succ t (k + 1 + j), qPoch_succ t k, qPoch_succ t j]
  have hk1 : (1 - t ^ (k + 1)) ≠ 0 := by
    have := hne (k + 1); rw [qPoch_succ] at this; exact right_ne_zero_of_mul this
  have hj1 : (1 - t ^ (j + 1)) ≠ 0 := by
    have := hne (j + 1); rw [qPoch_succ] at this; exact right_ne_zero_of_mul this
  have hk0 := hne k
  have hj0 := hne j
  field_simp
  ring

theorem exp_eq (m k : ℕ) (hk : k < m) : k * (k - 1) + 2 * m = (k + 1) * k + 2 * (m - k) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = k + 1 + j := ⟨m - (k + 1), by omega⟩
  rw [show k + 1 + j - k = j + 1 by omega]
  rcases k with _ | k
  · ring
  · simp only [Nat.add_sub_cancel]; ring

theorem qBinomial_finite : ∀ (s X : ℂ), ‖s‖ < 1 → ∀ m : ℕ, ∏ k ∈ Finset.range m, (1 + X * s ^ (2 * k)) = ∑ k ∈ Finset.range (m + 1), GlobalTheory.JacobiTriple.qBinom (s ^ 2) m k * s ^ (k * (k - 1)) * X ^ k := by
  intro s X hs m
  have ht : ‖s ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg s]
  induction m with
  | zero => simp [qBinom_zero_right _ ht]
  | succ m ih =>
    set f : ℕ → ℕ → ℂ := fun m k => qBinom (s ^ 2) m k * s ^ (k * (k - 1)) * X ^ k with hf
    change ∏ k ∈ Finset.range m, (1 + X * s ^ (2 * k)) = ∑ k ∈ Finset.range (m + 1), f m k at ih
    change _ = ∑ k ∈ Finset.range (m + 1 + 1), f (m + 1) k
    rw [Finset.prod_range_succ, ih, mul_add, mul_one]
    have A : ∑ k ∈ Finset.range (m + 1), f m k = f m 0 + ∑ k ∈ Finset.range m, f m (k + 1) := by
      rw [Finset.sum_range_succ', add_comm]
    have B : (∑ k ∈ Finset.range (m + 1), f m k) * (X * s ^ (2 * m)) =
        ∑ k ∈ Finset.range m, f m k * (X * s ^ (2 * m)) + f m m * (X * s ^ (2 * m)) := by
      rw [Finset.sum_mul, Finset.sum_range_succ]
    have C : ∑ k ∈ Finset.range (m + 1 + 1), f (m + 1) k =
        f (m + 1) 0 + ∑ k ∈ Finset.range m, f (m + 1) (k + 1) + f (m + 1) (m + 1) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ', add_comm (f (m + 1) 0)]
    have hsum : ∑ k ∈ Finset.range m, f (m + 1) (k + 1)
        = ∑ k ∈ Finset.range m, f m (k + 1) + ∑ k ∈ Finset.range m, f m k * (X * s ^ (2 * m)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk' := Finset.mem_range.mp hk
      simp only [hf]
      rw [qBinom_pascal _ ht m k hk']
      have : s ^ (k * (k - 1)) * s ^ (2 * m) = s ^ ((k + 1) * k) * (s ^ 2) ^ (m - k) := by
        rw [← pow_add, ← pow_mul, ← pow_add, exp_eq m k hk']
      simp only [Nat.add_sub_cancel]
      linear_combination (-(qBinom (s ^ 2) m k * X ^ (k + 1))) * this
    have hlast : s ^ ((m + 1) * (m + 1 - 1)) = s ^ (m * (m - 1)) * s ^ (2 * m) := by
      rw [← pow_add]; congr 1; rcases m with _ | m
      · simp
      · simp only [Nat.add_sub_cancel]; ring
    have e0 : f (m + 1) 0 = f m 0 := by
      simp only [hf, qBinom_zero_right _ ht]
    have em : f (m + 1) (m + 1) = f m m * (X * s ^ (2 * m)) := by
      simp only [hf, qBinom_self _ ht, hlast]; ring
    rw [B, A, C, hsum, e0, em]
    ring

end GlobalTheory.JacobiTriple.QBinomial
end

section

open Complex
open scoped Real

noncomputable section

namespace GlobalTheory.JacobiTriple

theorem finCoeff_tendsto_and_bounded :
    ∀ t : ℂ, ‖t‖ < 1 → (∀ j : ℤ, Filter.Tendsto (fun n : ℕ => GlobalTheory.JacobiTriple.finCoeff t n j)
      Filter.atTop (nhds (GlobalTheory.JacobiTriple.qPochInf t)⁻¹)) ∧
      ∃ C : ℝ, ∀ (n : ℕ) (j : ℤ), ‖GlobalTheory.JacobiTriple.finCoeff t n j‖ ≤ C := by
  intro t ht
  obtain ⟨hlim, hP0, hne⟩ := qPoch_tendsto t ht
  refine ⟨fun j => ?_, ?_⟩
  · have ha : Filter.Tendsto (fun n : ℕ => ((n : ℤ) + j).toNat) Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop_mono (f := fun n : ℕ => n - j.natAbs) (fun n => by omega) ?_
      exact Filter.tendsto_sub_atTop_nat _
    have hb : Filter.Tendsto (fun n : ℕ => 2 * n - ((n : ℤ) + j).toNat) Filter.atTop
        Filter.atTop := by
      refine Filter.tendsto_atTop_mono (f := fun n : ℕ => n - j.natAbs) (fun n => by omega) ?_
      exact Filter.tendsto_sub_atTop_nat _
    have h2 : Filter.Tendsto (fun n : ℕ => 2 * n) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono (fun n => by show n ≤ 2 * n; omega) Filter.tendsto_id
    have hmain : Filter.Tendsto (fun n : ℕ => qPoch t (2 * n) /
        (qPoch t ((n : ℤ) + j).toNat * qPoch t (2 * n - ((n : ℤ) + j).toNat))) Filter.atTop
        (nhds (qPochInf t / (qPochInf t * qPochInf t))) :=
      (hlim.comp h2).div ((hlim.comp ha).mul (hlim.comp hb)) (mul_ne_zero hP0 hP0)
    have hval : qPochInf t / (qPochInf t * qPochInf t) = (qPochInf t)⁻¹ := by
      field_simp
    rw [hval] at hmain
    refine hmain.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop j.natAbs] with n hn
    simp [finCoeff, qBinom, hn]
  · obtain ⟨B1, hB1⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto _ hlim)
    obtain ⟨B2, hB2⟩ := isBounded_iff_forall_norm_le.mp
      (Metric.isBounded_range_of_tendsto _ (hlim.inv₀ hP0))
    set B := max B1 B2
    have b1 : ∀ m, ‖qPoch t m‖ ≤ B := fun m => (hB1 _ ⟨m, rfl⟩).trans (le_max_left _ _)
    have b2 : ∀ m, ‖(qPoch t m)⁻¹‖ ≤ B := fun m => (hB2 _ ⟨m, rfl⟩).trans (le_max_right _ _)
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (b1 0)
    refine ⟨max (B ^ 3) 0, fun n j => ?_⟩
    unfold finCoeff
    split_ifs
    · unfold qBinom
      rw [div_eq_mul_inv, mul_inv, norm_mul, norm_mul]
      refine le_max_of_le_left ?_
      calc ‖qPoch t (2 * n)‖ * (‖(qPoch t ((n : ℤ) + j).toNat)⁻¹‖ *
            ‖(qPoch t (2 * n - ((n : ℤ) + j).toNat))⁻¹‖) ≤ B * (B * B) := by
            gcongr
            · exact b1 _
            · exact b2 _
            · exact b2 _
        _ = B ^ 3 := by ring
    · simp

end GlobalTheory.JacobiTriple
end
end

section

open Complex

theorem _root_.GlobalTheory.T.hasDerivAt_oddJacobiTheta_zero_eta_cube : GlobalTheory.ThetaWeberRoad.TripleProduct → ∀ τ : UpperHalfPlane, HasDerivAt (GlobalTheory.ThetaWeberRoad.oddTheta τ) (-2 * (Real.pi : ℂ) * ModularForm.eta (τ : ℂ) ^ 3) 0 := by
  first | exact @GlobalTheory.ThetaWeberRoad.OddDeriv.hasDerivAt_oddTheta_zero | exact GlobalTheory.ThetaWeberRoad.OddDeriv.hasDerivAt_oddTheta_zero | (intros; apply GlobalTheory.ThetaWeberRoad.OddDeriv.hasDerivAt_oddTheta_zero <;> assumption)
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory

theorem selfDual_real_mul_real_dual_eq_one :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (χ : V → V → ℂ), SelfDual μ χ → (∀ x x' y, χ (x + x') y = χ x y * χ x' y) → (∀ y, χ y 0 = 1) → ∀ L L' : AddSubgroup V, IsCompact (L : Set V) → IsOpen (L : Set V) → IsCompact (L' : Set V) → IsOpen (L' : Set V) → (∀ y, y ∈ L' ↔ ∀ x ∈ L, χ x y = 1) → μ.real (L : Set V) * μ.real (L' : Set V) = 1 := by
  intro V _ _ _ _ _ μ χ hsd hadd h0 L L' hLc hLo hL'c hL'o hdual
  obtain ⟨hH, hinv⟩ := hsd
  set Φ : V → ℂ := (L : Set V).indicator (fun _ => (1 : ℂ)) with hΦ
  have hclopen : IsClopen (L : Set V) := ⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩
  have hcont : Continuous Φ := hclopen.continuous_indicator continuous_const
  have hsupp : HasCompactSupport Φ :=
    HasCompactSupport.intro hLc (fun x hx => Set.indicator_of_notMem hx _)
  have htr : (fun y => ∫ x, Φ x * χ x y ∂μ)
      = (L' : Set V).indicator (fun _ => ((μ.real (L : Set V) : ℝ) : ℂ)) := by
    funext y
    by_cases hy : y ∈ L'
    · rw [Set.indicator_of_mem (show y ∈ (L' : Set V) from hy)]
      have : (fun x => Φ x * χ x y) = Φ := by
        funext x
        by_cases hx : x ∈ L
        · rw [(hdual y).1 hy x hx, mul_one]
        · simp [hΦ, Set.indicator_of_notMem (show x ∉ (L : Set V) from hx)]
      rw [this, hΦ, integral_indicator_const _ hLo.measurableSet]
      simp
    · rw [Set.indicator_of_notMem (show y ∉ (L' : Set V) from hy)]
      have hy' := mt (hdual y).2 hy
      push Not at hy'
      obtain ⟨x0, hx0, hne⟩ := hy'
      have h1 := integral_add_left_eq_self (μ := μ) (fun x => Φ x * χ x y) x0
      have h2 : (fun x => Φ (x0 + x) * χ (x0 + x) y) = fun x => χ x0 y * (Φ x * χ x y) := by
        funext x
        have : Φ (x0 + x) = Φ x := by
          by_cases hx : x ∈ L
          · simp [hΦ, Set.indicator_of_mem (show x ∈ (L : Set V) from hx),
              Set.indicator_of_mem (show x0 + x ∈ (L : Set V) from L.add_mem hx0 hx)]
          · have hx' : x0 + x ∉ L := fun h => hx ((L.add_mem_cancel_left hx0).1 h)
            simp [hΦ, Set.indicator_of_notMem (show x ∉ (L : Set V) from hx),
              Set.indicator_of_notMem (show x0 + x ∉ (L : Set V) from hx')]
        rw [this, hadd]; ring
      rw [h2, integral_const_mul] at h1
      have h3 : (χ x0 y - 1) * ∫ x, Φ x * χ x y ∂μ = 0 := by rw [sub_mul, h1]; ring
      exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hne)
  have hint : Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ := by
    rw [htr, integrable_indicator_iff hL'o.measurableSet]
    exact integrableOn_const hL'c.measure_lt_top.ne
  have key := hinv Φ hcont hsupp hint 0
  simp only [h0, mul_one, neg_zero] at key
  rw [htr, integral_indicator_const _ hL'o.measurableSet, hΦ,
    Set.indicator_of_mem (show (0 : V) ∈ (L : Set V) from L.zero_mem)] at key
  rw [Complex.real_smul, mul_comm] at key
  exact_mod_cast key

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.mem_of_finiteDimensional_span_rightTranslates' : ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] (R : Subalgebra ℂ (K → ℂ)), (∀ p ∈ R, Continuous p) → (∀ p ∈ R, star p ∈ R) → (∀ x y : K, x ≠ y → ∃ p ∈ R, p x ≠ p y) → (∀ p ∈ R, ∃ (m : ℕ) (a b : Fin m → K → ℂ), (∀ i, a i ∈ R ∧ Continuous (b i)) ∧ ∀ x k, p (x⁻¹ * k) = ∑ i, a i x * b i k) → ∀ f : K → ℂ, Continuous f → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun x : K => f (x * k))) → f ∈ R := by
  first | exact @GlobalTheory.UnitaryBC.mem_of_finiteDimensional_span_rightTranslates | exact GlobalTheory.UnitaryBC.mem_of_finiteDimensional_span_rightTranslates | (intros; apply GlobalTheory.UnitaryBC.mem_of_finiteDimensional_span_rightTranslates <;> assumption)
end
