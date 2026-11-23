module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.Filter.AtTopBot.Interval
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.FloorTelescope

lemma sum_Icc_sub (G : ℤ → ℂ) (R : ℕ) :
    ∑ d ∈ Finset.Icc (-(R:ℤ)) R, (G (d+1) - G d) = G ((R:ℤ)+1) - G (-(R:ℤ)) := by
  have himg : Finset.Icc (-(R:ℤ)) R = (Finset.range (2*R+1)).image (fun k : ℕ => (k:ℤ) - R) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(d + R).toNat, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      omega
  rw [himg, Finset.sum_image (by intro a _ b _ h; simp only at h; omega)]
  have := Finset.sum_range_sub (fun k : ℕ => G ((k:ℤ) - R)) (2*R+1)
  convert this using 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    congr 2; push_cast; ring
  · congr 2 <;> push_cast <;> ring

theorem tendsto_sum_Icc_div (L : ℕ) (φ : ZMod L → ℂ) (z : ℂ) (hL : 0 < L) (hz : 0 < z.im)
    (h0 : hat φ 0 = 0) :
    Tendsto (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R:ℤ)) R, φ d * (z + (L * (d / L) : ℤ))⁻¹) atTop (𝓝 0) := by
  have hsum : ∑ y ∈ Finset.range L, φ y = 0 := by simpa [hat] using h0
  have hLz : (0:ℤ) < L := by exact_mod_cast hL
  obtain ⟨u, hu⟩ : ∃ u : ℤ → ℂ, ∀ d, u d = (z + ((L * (d / L) : ℤ) : ℂ))⁻¹ := ⟨_, fun _ => rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℤ → ℂ, ∀ d, Φ d = ∑ e ∈ Finset.range (d % L).toNat, φ e := ⟨_, fun _ => rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℤ → ℂ, ∀ d, F d = Φ d * u d := ⟨_, fun _ => rfl⟩
  have key : ∀ d : ℤ, φ d * u d = F (d+1) - F d := by
    intro d
    have hdiv := Int.mul_ediv_add_emod d L
    have h1 := Int.emod_nonneg d hLz.ne'
    have h2 := Int.emod_lt_of_pos d hLz
    have hcast : (((d % L).toNat : ℕ) : ZMod L) = (d : ZMod L) := by
      have : ((((d % L).toNat : ℕ) : ℤ) : ZMod L) = ((d % L : ℤ) : ZMod L) := by
        rw [Int.toNat_of_nonneg h1]
      rw [Int.cast_natCast] at this
      rw [this, ZMod.intCast_mod]
    rcases lt_or_eq_of_le (show d % L + 1 ≤ L by omega) with hlt | heq
    · have hq : (d+1) / L = d / L := by
        have h3 : d + 1 = (d % L + 1) + L * (d / L) := by omega
        rw [h3, Int.add_mul_ediv_left _ _ hLz.ne', Int.ediv_eq_zero_of_lt (by omega) hlt, zero_add]
      have hr : (d+1) % L = d % L + 1 := by
        have := Int.mul_ediv_add_emod (d+1) L
        rw [hq] at this; omega
      have hu' : u (d+1) = u d := by rw [hu, hu, hq]
      have hΦ' : Φ (d+1) = Φ d + φ d := by
        rw [hΦ, hΦ, hr, show (d % L + 1).toNat = (d % L).toNat + 1 by omega, Finset.sum_range_succ, hcast]
      rw [hF, hF, hu', hΦ']; ring
    · have hq : (d+1) / L = d / L + 1 := by
        rw [show d + 1 = L * (d / L + 1) by linarith, Int.mul_ediv_cancel_left _ hLz.ne']
      have hr : (d+1) % L = 0 := by
        have := Int.mul_ediv_add_emod (d+1) L
        rw [hq] at this; linarith
      have hΦ0 : Φ (d+1) = 0 := by rw [hΦ, hr]; simp
      have hn : (d % L).toNat = L - 1 := by omega
      have hs := Finset.sum_range_succ (fun e : ℕ => φ (e : ZMod L)) (L-1)
      rw [Nat.sub_add_cancel hL, ← hn, hcast, hsum] at hs
      have hΦd : Φ d = - φ d := by rw [hΦ]; linear_combination -hs
      rw [hF, hF, hΦ0, hΦd]; ring
  have hfun : (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R:ℤ)) R, φ d * (z + (L * (d / L) : ℤ))⁻¹)
      = fun R : ℕ => F ((R:ℤ)+1) - F (-(R:ℤ)) := by
    funext R
    rw [← sum_Icc_sub]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← key, hu]
  rw [hfun]
  set M : ℝ := ∑ y ∈ Finset.range L, ‖φ y‖
  have hM : ∀ d, ‖Φ d‖ ≤ M := by
    intro d
    rw [hΦ]
    have h2 := Int.emod_lt_of_pos d hLz
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.2 (by omega)) (fun _ _ _ => norm_nonneg _))
  have uLim : ∀ m : ℕ → ℤ, (∀ R : ℕ, (R:ℝ) - L ≤ |((m R : ℤ) : ℝ)|) →
      Tendsto (fun R : ℕ => (z + ((m R : ℤ) : ℂ))⁻¹) atTop (𝓝 0) := by
    intro m hm
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_inv]
    apply Tendsto.inv_tendsto_atTop
    refine tendsto_atTop_mono (fun R => ?_)
      (tendsto_atTop_add_const_right _ (-(L:ℝ) - ‖z‖) tendsto_natCast_atTop_atTop)
    have h1 : ‖((m R : ℤ) : ℂ)‖ ≤ ‖z + ((m R : ℤ) : ℂ)‖ + ‖z‖ := by
      calc ‖((m R : ℤ) : ℂ)‖ = ‖(z + ((m R : ℤ) : ℂ)) - z‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    rw [Complex.norm_intCast] at h1
    linarith [hm R]
  have hFb : ∀ x, ‖F x‖ ≤ M * ‖(z + ((L * (x / L) : ℤ) : ℂ))⁻¹‖ := by
    intro x
    rw [hF, norm_mul, ← hu]
    exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
  have hA : Tendsto (fun R : ℕ => F ((R:ℤ)+1)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun R => hFb _) ?_
    have hm : ∀ R : ℕ, (R:ℝ) - L ≤ |(((L * (((R:ℤ)+1) / L) : ℤ)) : ℝ)| := by
      intro R
      have e1 := Int.mul_ediv_add_emod ((R:ℤ)+1) L
      have e2 := Int.emod_lt_of_pos ((R:ℤ)+1) hLz
      have : (R:ℤ) - L ≤ L * (((R:ℤ)+1) / L) := by linarith
      have := (Int.cast_le (R := ℝ)).2 this
      rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast] at this
      exact this.trans (le_abs_self _)
    simpa only [norm_zero, mul_zero] using ((uLim _ hm).norm.const_mul M)
  have hB : Tendsto (fun R : ℕ => F (-(R:ℤ))) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun R => hFb _) ?_
    have hm : ∀ R : ℕ, (R:ℝ) - L ≤ |(((L * ((-(R:ℤ)) / L) : ℤ)) : ℝ)| := by
      intro R
      have e1 := Int.mul_ediv_add_emod (-(R:ℤ)) L
      have e2 := Int.emod_nonneg (-(R:ℤ)) hLz.ne'
      have : (R:ℤ) - L ≤ -(L * ((-(R:ℤ)) / L)) := by linarith
      have := (Int.cast_le (R := ℝ)).2 this
      rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, Int.cast_neg] at this
      exact this.trans (neg_le_abs _)
    simpa only [norm_zero, mul_zero] using ((uLim _ hm).norm.const_mul M)
  simpa using hA.sub hB

end GlobalTheory.FloorTelescope
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.RowLim

noncomputable def symS (f : ℤ → ℂ) (R : ℕ) : ℂ := ∑ d ∈ Finset.Icc (-(R : ℤ)) R, f d

lemma symS_succ (f : ℤ → ℂ) (R : ℕ) :
    symS f (R + 1) = f (-((R : ℤ) + 1)) + (f ((R : ℤ) + 1) + symS f R) := by
  unfold symS
  have h : Finset.Icc (-((R + 1 : ℕ) : ℤ)) ((R + 1 : ℕ) : ℤ)
      = insert (-((R : ℤ) + 1)) (insert ((R : ℤ) + 1) (Finset.Icc (-(R : ℤ)) R)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
  rw [h, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
    Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]

lemma symS_shift_one (f : ℤ → ℂ) (R : ℕ) :
    symS (fun d => f (d + 1)) R - symS f R = f ((R : ℤ) + 1) - f (-(R : ℤ)) := by
  induction R with
  | zero => simp [symS]
  | succ R ih =>
    rw [symS_succ, symS_succ]
    push_cast
    have e1 : -((R : ℤ) + 1) + 1 = -(R : ℤ) := by ring
    rw [e1]
    linear_combination ih

lemma tendsto_atTop_of_cofinite {f : ℤ → ℂ} (hf : Tendsto f cofinite (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := hf.mono_left (by rw [Int.cofinite_eq]; exact le_sup_right)

lemma tendsto_atBot_of_cofinite {f : ℤ → ℂ} (hf : Tendsto f cofinite (𝓝 0)) :
    Tendsto f atBot (𝓝 0) := hf.mono_left (by rw [Int.cofinite_eq]; exact le_sup_left)

lemma shift_tendsto {f : ℤ → ℂ} (hf : Tendsto f cofinite (𝓝 0)) (r : ℤ) :
    Tendsto (fun d => f (d + r)) cofinite (𝓝 0) :=
  hf.comp (add_left_injective r).tendsto_cofinite

lemma symS_shift_tendsto (r : ℕ) : ∀ f : ℤ → ℂ, Tendsto f cofinite (𝓝 0) →
    Tendsto (fun R => symS (fun d => f (d + r)) R - symS f R) atTop (𝓝 0) := by
  induction r with
  | zero => intro f _; simp
  | succ r ih =>
    intro f hf
    have h1 := ih (fun e => f (e + 1)) (shift_tendsto hf 1)
    have hR : Tendsto (fun R : ℕ => (R : ℤ)) atTop atTop := tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun R : ℕ => f ((R : ℤ) + 1) - f (-(R : ℤ))) atTop (𝓝 0) := by
      have a := (tendsto_atTop_of_cofinite hf).comp (tendsto_atTop_add_const_right _ 1 hR)
      have b := (tendsto_atBot_of_cofinite hf).comp (tendsto_neg_atTop_atBot.comp hR)
      simpa using a.sub b
    have := h1.add ((tendsto_congr (fun R => (symS_shift_one f R).symm)).1 h2)
    rw [add_zero] at this
    refine (tendsto_congr fun R => ?_).1 this
    have e : (fun d : ℤ => f (d + ((r + 1 : ℕ) : ℤ))) = fun d => f (d + (r : ℤ) + 1) := by
      funext d; push_cast; ring_nf
    beta_reduce
    rw [e]; ring

noncomputable def mean (L : ℕ) (k : ℤ → ℂ) (d : ℤ) : ℂ := (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L, k (d + r)

lemma mean_tendsto {L : ℕ} {k : ℤ → ℂ} (hk : Tendsto k cofinite (𝓝 0)) :
    Tendsto (mean L k) cofinite (𝓝 0) := by
  have : Tendsto (fun d => ∑ r ∈ Finset.range L, k (d + r)) cofinite (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.range L) fun r _ => shift_tendsto hk r
  have h2 := this.const_mul ((L : ℂ)⁻¹)
  rw [mul_zero] at h2
  exact h2

lemma bdd_mul_tendsto {A k : ℤ → ℂ} {C : ℝ} (hA : ∀ d, ‖A d‖ ≤ C)
    (hk : Tendsto k cofinite (𝓝 0)) : Tendsto (fun d => A d * k d) cofinite (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero] at hk ⊢
  refine squeeze_zero (fun _ => norm_nonneg _) (fun d => ?_) (by simpa using hk.const_mul C)
  rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hA d) (norm_nonneg _)

lemma symS_mul_mean_tendsto {L : ℕ} {A k : ℤ → ℂ} {C : ℝ} (hA : ∀ d, ‖A d‖ ≤ C)
    (hsum : ∀ d, ∑ r ∈ Finset.range L, A (d - r) = 0) (hk : Tendsto k cofinite (𝓝 0)) :
    Tendsto (symS fun d => A d * mean L k d) atTop (𝓝 0) := by
  set f : ℕ → ℤ → ℂ := fun r e => A (e - r) * k e with hf
  have eq : ∀ R, symS (fun d => A d * mean L k d) R
      = (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L, (symS (fun d => f r (d + r)) R - symS (f r) R) := by
    intro R
    have h0 : ∑ r ∈ Finset.range L, symS (f r) R = 0 := by
      simp only [symS, hf]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun d _ => ?_
      rw [← Finset.sum_mul, hsum, zero_mul]
    rw [Finset.sum_sub_distrib, h0, sub_zero]
    simp only [symS, mean, hf, add_sub_cancel_right]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  rw [show (symS fun d => A d * mean L k d) = _ from funext eq]
  have := tendsto_finsetSum (Finset.range L) fun r _ =>
    symS_shift_tendsto r (f r) (bdd_mul_tendsto (fun d => hA (d - r)) hk)
  simpa using this.const_mul ((L : ℂ)⁻¹)

theorem rowlim : ∀ (L : ℕ) (A g : ℤ → ℂ) (G : ℤ × ℤ → ℂ) (c : ℤ), 0 < L → (∃ C : ℝ, ∀ d, ‖A d‖ ≤ C) → (∀ d, ∑ r ∈ Finset.range L, A (d - r) = 0) → (∀ d, G (c, d) = g d) → Tendsto g cofinite (𝓝 0) → (Summable fun d : ℤ => A d * dif L (0, 1) (dif L (0, 1) G) (c, d)) → Tendsto (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R : ℤ)) R, A d * g d) atTop (𝓝 (∑' d : ℤ, A d * dif L (0, 1) (dif L (0, 1) G) (c, d))) := by
  intro L A g G c _ ⟨C, hA⟩ hsum hG hg hS
  have hpt : ∀ (F : ℤ × ℤ → ℂ) (d : ℤ), dif L (0, 1) F (c, d) = F (c, d) - mean L (fun e => F (c, e)) d := by
    intro F d
    have e : ∀ r : ℕ, (c, d) + (r : ℤ) • ((0 : ℤ), (1 : ℤ)) = (c, d + r) := by
      intro r; ext <;> simp
    simp only [dif, mean, e]
  set h : ℤ → ℂ := fun d => g d - mean L g d with hh
  have hG1 : ∀ d, dif L (0, 1) G (c, d) = h d := by
    intro d; rw [hpt]; simp only [hh, hG]
  have hG2 : ∀ d, dif L (0, 1) (dif L (0, 1) G) (c, d) = h d - mean L h d := by
    intro d; rw [hpt, hG1]; simp only [hG1]
  simp only [hG2] at hS ⊢
  have hTs := (hS.hasSum.comp Finset.tendsto_Icc_neg)
  have hh0 : Tendsto h cofinite (𝓝 0) := by simpa using hg.sub (mean_tendsto hg)
  have k1 := symS_mul_mean_tendsto hA hsum hg
  have k2 := symS_mul_mean_tendsto hA hsum hh0
  have := (hTs.add k1).add k2
  rw [add_zero, add_zero] at this
  refine (tendsto_congr fun R => ?_).1 this
  simp only [Function.comp, symS, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [hh]; ring

end GlobalTheory.RowLim
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.Lin

theorem norm_term (n : ℕ) (τ : ℍ) :
    ‖cexp (2 * π * Complex.I * n * τ)‖ = (Real.exp (-2 * π * τ.im)) ^ n := by
  rw [Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem summ_norm (a : ℕ → ℂ) (ha : PolyB a) (τ : ℍ) :
    Summable fun n : ℕ => ‖a n * cexp (2 * π * Complex.I * n * τ)‖ := by
  obtain ⟨C, A, hC⟩ := ha
  set r := Real.exp (-2 * π * τ.im) with hr
  have r0 : 0 < r := Real.exp_pos _
  have r1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    have := τ.im_pos
    have := Real.pi_pos
    nlinarith
  have hs : Summable fun n : ℕ => ((n : ℝ)) ^ A * r ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one A (by rw [Real.norm_eq_abs, abs_of_pos r0]; exact r1)
  have hs1 : Summable fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ A * r ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr hs
  have hs2 : Summable fun n : ℕ => C * (((n : ℝ) + 1) ^ A * r ^ n) := by
    apply Summable.mul_left
    have := hs1.mul_right r⁻¹
    refine this.congr (fun n => ?_)
    push_cast
    rw [pow_succ]
    field_simp
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hs2
  rw [norm_mul, norm_term, ← hr, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hC n) (pow_nonneg r0.le _)

theorem summ (a : ℕ → ℂ) (ha : PolyB a) (τ : ℍ) :
    Summable fun n : ℕ => a n * cexp (2 * π * Complex.I * n * τ) :=
  (summ_norm a ha τ).of_norm

theorem polyB_zero : PolyB (0 : ℕ → ℂ) := ⟨0, 0, fun n => by simp⟩

theorem polyB_add (a b : ℕ → ℂ) (ha : PolyB a) (hb : PolyB b) : PolyB (a + b) := by
  obtain ⟨C, A, hC⟩ := ha
  obtain ⟨D, B, hD⟩ := hb
  refine ⟨|C| + |D|, A + B, fun n => ?_⟩
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := n.cast_nonneg (α := ℝ); linarith
  have hA : ((n : ℝ) + 1) ^ A ≤ ((n : ℝ) + 1) ^ (A + B) := pow_le_pow_right₀ h1 (by omega)
  have hB : ((n : ℝ) + 1) ^ B ≤ ((n : ℝ) + 1) ^ (A + B) := pow_le_pow_right₀ h1 (by omega)
  have p0 : 0 ≤ ((n : ℝ) + 1) ^ A := by positivity
  have p1 : 0 ≤ ((n : ℝ) + 1) ^ B := by positivity
  calc ‖(a + b) n‖ ≤ ‖a n‖ + ‖b n‖ := norm_add_le _ _
    _ ≤ C * ((n : ℝ) + 1) ^ A + D * ((n : ℝ) + 1) ^ B := add_le_add (hC n) (hD n)
    _ ≤ |C| * ((n : ℝ) + 1) ^ (A + B) + |D| * ((n : ℝ) + 1) ^ (A + B) := by
        apply add_le_add
        · exact (mul_le_mul_of_nonneg_right (le_abs_self C) p0).trans
            (mul_le_mul_of_nonneg_left hA (abs_nonneg C))
        · exact (mul_le_mul_of_nonneg_right (le_abs_self D) p1).trans
            (mul_le_mul_of_nonneg_left hB (abs_nonneg D))
    _ = (|C| + |D|) * ((n : ℝ) + 1) ^ (A + B) := by ring

theorem polyB_smul (c : ℂ) (a : ℕ → ℂ) (ha : PolyB a) : PolyB (c • a) := by
  obtain ⟨C, A, hC⟩ := ha
  refine ⟨‖c‖ * C, A, fun n => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC n) (norm_nonneg c)

theorem qs_zero : qs (0 : ℕ → ℂ) = 0 := by
  funext τ; simp [qs]

theorem qs_add (a b : ℕ → ℂ) (ha : PolyB a) (hb : PolyB b) : qs (a + b) = qs a + qs b := by
  funext τ
  simp only [qs, Pi.add_apply, add_mul]
  exact (summ a ha τ).tsum_add (summ b hb τ)

theorem qs_smul (c : ℂ) (a : ℕ → ℂ) : qs (c • a) = c • qs a := by
  funext τ
  simp only [qs, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact tsum_mul_left

theorem coprime_of_level (L : ℕ) (γ : SL(2, ℤ)) (h : (L : ℤ) ∣ γ 1 0) : IsCoprime (γ 1 1) (L : ℤ) := by
  obtain ⟨m, hm⟩ := h
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    exact this
  refine ⟨γ 0 0, -(γ 0 1 * m), ?_⟩
  rw [hm] at hdet
  linear_combination hdet

end GlobalTheory.EisM.Lin

open GlobalTheory.EisM.Lin in
theorem GlobalTheory.EisM.mf_linear : ∀ (k L : ℕ) (χ : ℤ → ℂ), (MF k L χ 0) ∧ (∀ a b, MF k L χ a → MF k L χ b → MF k L χ (a + b) ∧ qs (a + b) = qs a + qs b) ∧ (∀ (c : ℂ) a, MF k L χ a → MF k L χ (c • a) ∧ qs (c • a) = c • qs a) ∧ (∀ χ' a, (∀ d : ℤ, IsCoprime d L → χ d = χ' d) → MF k L χ a → MF k L χ' a) ∧ (∀ L' a, L ∣ L' → MF k L χ a → MF k L' χ a) ∧ (∀ L' a, L ∣ L' → CF k L χ a → CF k L' χ a) := by
  intro k L χ
  have lev : ∀ L' a, L ∣ L' → MF k L χ a → MF k L' χ a := by
    intro L' a hL ⟨hp, hi⟩
    refine ⟨hp, fun γ hγ τ => hi γ ?_ τ⟩
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hL) hγ
  refine ⟨⟨polyB_zero, fun γ _ τ => by simp [qs_zero]⟩, ?_, ?_, ?_, lev, ?_⟩
  · intro a b ⟨ha, ia⟩ ⟨hb, ib⟩
    have e := qs_add a b ha hb
    refine ⟨⟨polyB_add a b ha hb, fun γ hγ τ => ?_⟩, e⟩
    rw [e, Pi.add_apply, Pi.add_apply, ia γ hγ τ, ib γ hγ τ]
    ring
  · intro c a ⟨ha, ia⟩
    have e := qs_smul c a
    refine ⟨⟨polyB_smul c a ha, fun γ hγ τ => ?_⟩, e⟩
    rw [e, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, ia γ hγ τ]
    ring
  · intro χ' a hχ ⟨ha, ia⟩
    refine ⟨ha, fun γ hγ τ => ?_⟩
    rw [ia γ hγ τ, hχ _ (coprime_of_level L γ hγ)]
  · intro L' a hL ⟨hm, hc⟩
    exact ⟨lev L' a hL hm, hc⟩
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem qterm_norm (n : ℕ) (τ : ℍ) :
    ‖cexp (2 * π * Complex.I * n * τ)‖ = Real.exp (-2 * π * τ.im) ^ n := by
  rw [Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem summable_succ_pow_mul_geom (A : ℕ) {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ A * r ^ n := by
  have hs : Summable fun n : ℕ => (n : ℝ) ^ A * r ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one A (by rw [Real.norm_eq_abs, abs_of_pos h0]; exact h1)
  have hs' : Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ A * r ^ (n + 1) :=
    (summable_nat_add_iff 1).2 hs
  have := hs'.mul_left r⁻¹
  refine this.congr fun n => ?_
  push_cast
  rw [pow_succ]
  field_simp

theorem qterm_bound {a : ℕ → ℂ} {C : ℝ} {A : ℕ} (hC : ∀ n : ℕ, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ A)
    {y₀ : ℝ} (n : ℕ) (τ : ℍ) (hτ : y₀ ≤ τ.im) :
    ‖a n * cexp (2 * π * Complex.I * n * τ)‖ ≤ C * ((n : ℝ) + 1) ^ A * Real.exp (-2 * π * y₀) ^ n := by
  rw [norm_mul, qterm_norm]
  have h1 : Real.exp (-2 * π * τ.im) ^ n ≤ Real.exp (-2 * π * y₀) ^ n := by
    apply pow_le_pow_left₀ (Real.exp_pos _).le
    apply Real.exp_le_exp.2
    nlinarith [Real.pi_pos]
  calc ‖a n‖ * Real.exp (-2 * π * τ.im) ^ n ≤ C * ((n : ℝ) + 1) ^ A * Real.exp (-2 * π * τ.im) ^ n :=
        mul_le_mul_of_nonneg_right (hC n) (by positivity)
    _ ≤ C * ((n : ℝ) + 1) ^ A * Real.exp (-2 * π * y₀) ^ n := by
        apply mul_le_mul_of_nonneg_left h1
        exact le_trans (norm_nonneg _) (hC n)

theorem qterm_summable_bound {C : ℝ} (A : ℕ) {y₀ : ℝ} (hy : 0 < y₀) :
    Summable fun n : ℕ => C * ((n : ℝ) + 1) ^ A * Real.exp (-2 * π * y₀) ^ n := by
  have h := summable_succ_pow_mul_geom A (r := Real.exp (-2 * π * y₀)) (Real.exp_pos _)
    (Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos]))
  simpa [mul_assoc] using h.mul_left C

theorem qs_summable_continuous : ∀ a : ℕ → ℂ, PolyB a →
    (∀ τ : ℍ, Summable fun n : ℕ => ‖a n * cexp (2 * π * Complex.I * n * τ)‖) ∧ Continuous (qs a) := by
  intro a ⟨C, A, hC⟩
  refine ⟨fun τ => ?_, ?_⟩
  · exact (qterm_summable_bound (C := C) A τ.im_pos).of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => qterm_bound hC n τ le_rfl)
  · rw [continuous_iff_continuousAt]
    intro τ₀
    have hy : 0 < τ₀.im / 2 := half_pos τ₀.im_pos
    have hopen : IsOpen {τ : ℍ | τ₀.im / 2 < τ.im} :=
      isOpen_lt continuous_const UpperHalfPlane.continuous_im
    have hmem : τ₀ ∈ {τ : ℍ | τ₀.im / 2 < τ.im} := by
      show τ₀.im / 2 < τ₀.im
      linarith [τ₀.im_pos]
    have hon : ContinuousOn (qs a) {τ : ℍ | τ₀.im / 2 < τ.im} := by
      unfold qs
      refine continuousOn_tsum (fun n => ?_) (qterm_summable_bound (C := C) A hy) ?_
      · apply Continuous.continuousOn
        fun_prop
      · intro n τ hτ
        exact qterm_bound hC n τ (le_of_lt hτ)
    exact hon.continuousAt (hopen.mem_nhds hmem)

end GlobalTheory.EisM
end
