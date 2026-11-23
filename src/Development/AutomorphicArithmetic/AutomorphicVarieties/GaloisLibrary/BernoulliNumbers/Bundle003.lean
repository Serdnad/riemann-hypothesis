module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.Real.Pi.Bounds
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
public import Mathlib.NumberTheory.ZetaValues
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Fourier.AddCircle

@[expose] public section

section

open Finset UpperTheory.V.Bern

private lemma hd_cpow (c : ℂ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => (x : ℂ) ^ c) (c * (t : ℂ) ^ (c - 1)) t := by
  have hmem : ((t : ℂ)) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 ht
  exact (Complex.hasStrictDerivAt_cpow_const (c := c) hmem).hasDerivAt.comp_ofReal

private lemma lip (s : ℂ) (a x y : ℝ) (ha : 0 < a) (hx : a ≤ x) (hy : a ≤ y) (hs : -2 ≤ s.re) :
    ‖(y : ℂ) ^ (-s - 1) - (x : ℂ) ^ (-s - 1)‖ ≤ ‖s + 1‖ * a ^ (-s.re - 2) * ‖y - x‖ := by
  have hge : ∀ z ∈ Set.uIcc x y, a ≤ z := by
    intro z hz
    rcases Set.mem_uIcc.1 hz with h | h
    · exact le_trans hx h.1
    · exact le_trans hy h.1
  have hder : ∀ z ∈ Set.uIcc x y, HasDerivWithinAt (fun w : ℝ => (w : ℂ) ^ (-s - 1))
      ((-s - 1) * (z : ℂ) ^ (-s - 1 - 1)) (Set.uIcc x y) z := by
    intro z hz
    exact (hd_cpow (-s - 1) z (lt_of_lt_of_le ha (hge z hz))).hasDerivWithinAt
  have hbd : ∀ z ∈ Set.uIcc x y, ‖(-s - 1) * (z : ℂ) ^ (-s - 1 - 1)‖ ≤ ‖s + 1‖ * a ^ (-s.re - 2) := by
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le ha (hge z hz)
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hz0]
    have h1 : ‖-s - 1‖ = ‖s + 1‖ := by
      rw [show -s - 1 = -(s + 1) by ring, norm_neg]
    have h2 : (-s - 1 - 1).re = -s.re - 2 := by
      simp; ring
    rw [h1, h2]
    have h3 : z ^ (-s.re - 2) ≤ a ^ (-s.re - 2) :=
      Real.rpow_le_rpow_of_nonpos ha (hge z hz) (show -s.re - 2 ≤ 0 by linarith)
    exact mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd (convex_uIcc x y)
    Set.left_mem_uIcc Set.right_mem_uIcc

theorem UpperTheory.V.Bern.b_taylor2 :
    ∀ (s : ℂ) (a u v : ℝ), 0 < a → a ≤ u → a ≤ v → -2 ≤ s.re → ‖(v : ℂ) ^ (-s) - (u : ℂ) ^ (-s) + s * ((v : ℂ) - u) * (u : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * ‖s + 1‖ * a ^ (-s.re - 2) * (v - u) ^ 2 := by
  intro s a u v ha hu hv hs
  have hge : ∀ z ∈ Set.uIcc u v, a ≤ z := by
    intro z hz
    rcases Set.mem_uIcc.1 hz with h | h
    · exact le_trans hu h.1
    · exact le_trans hv h.1
  set g : ℝ → ℂ := fun x => (x : ℂ) ^ (-s) - (u : ℂ) ^ (-s) + s * ((x : ℂ) - u) * (u : ℂ) ^ (-s - 1) with hg
  have hder : ∀ z ∈ Set.uIcc u v, HasDerivWithinAt g
      (-s * (z : ℂ) ^ (-s - 1) + s * (u : ℂ) ^ (-s - 1)) (Set.uIcc u v) z := by
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le ha (hge z hz)
    have h1 := hd_cpow (-s) z hz0
    have h2 : HasDerivAt (fun x : ℝ => s * ((x : ℂ) - u) * (u : ℂ) ^ (-s - 1))
        (s * 1 * (u : ℂ) ^ (-s - 1)) z :=
      (((hasDerivAt_id z).ofReal_comp.sub_const (u : ℂ)).const_mul s).mul_const _
    have h3 := (h1.sub_const ((u : ℂ) ^ (-s))).add h2
    simp only [mul_one] at h3
    exact h3.hasDerivWithinAt
  have hbd : ∀ z ∈ Set.uIcc u v, ‖-s * (z : ℂ) ^ (-s - 1) + s * (u : ℂ) ^ (-s - 1)‖ ≤
      ‖s‖ * ‖s + 1‖ * a ^ (-s.re - 2) * ‖v - u‖ := by
    intro z hz
    have he : -s * (z : ℂ) ^ (-s - 1) + s * (u : ℂ) ^ (-s - 1) =
        s * ((u : ℂ) ^ (-s - 1) - (z : ℂ) ^ (-s - 1)) := by ring
    rw [he, norm_mul]
    have hl := lip s a z u ha (hge z hz) hu hs
    have hd : ‖u - z‖ ≤ ‖v - u‖ := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm]
      exact Set.abs_sub_left_of_mem_uIcc hz
    have hC : 0 ≤ ‖s + 1‖ * a ^ (-s.re - 2) := by positivity
    calc ‖s‖ * ‖(u : ℂ) ^ (-s - 1) - (z : ℂ) ^ (-s - 1)‖
        ≤ ‖s‖ * (‖s + 1‖ * a ^ (-s.re - 2) * ‖u - z‖) := by gcongr
      _ ≤ ‖s‖ * (‖s + 1‖ * a ^ (-s.re - 2) * ‖v - u‖) := by gcongr
      _ = ‖s‖ * ‖s + 1‖ * a ^ (-s.re - 2) * ‖v - u‖ := by ring
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd (convex_uIcc u v)
    Set.left_mem_uIcc Set.right_mem_uIcc
  have hgu : g u = 0 := by simp [hg]
  have hgv : g v = (v : ℂ) ^ (-s) - (u : ℂ) ^ (-s) + s * ((v : ℂ) - u) * (u : ℂ) ^ (-s - 1) := rfl
  rw [hgu, sub_zero, hgv] at key
  calc _ ≤ _ := key
    _ = ‖s‖ * ‖s + 1‖ * a ^ (-s.re - 2) * (v - u) ^ 2 := by
      rw [Real.norm_eq_abs, mul_assoc _ |v - u| |v - u|, ← sq, sq_abs]
end

section

open Finset UpperTheory.V.Bern

private theorem polybound_cast (k : ℕ) (x : ℚ) :
    (((Polynomial.bernoulli k).eval x : ℚ) : ℝ) = bernoulliFun k (x : ℝ) := by
  rw [bernoulliFun, Polynomial.eval_map_algebraMap, ← eq_ratCast (algebraMap ℚ ℝ) x,
    Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, eq_ratCast]

private theorem polybound_norm_fourier (n : ℤ) (y : UnitAddCircle) : ‖fourier n y‖ = 1 := by
  rw [fourier_apply]; exact Circle.norm_coe _

private theorem polybound_big {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (2 * Real.pi) ^ k / (k.factorial : ℝ) * |bernoulliFun k x| ≤ 4 := by
  have hs := hasSum_one_div_nat_pow_mul_fourier hk hx
  have h2 : ∀ (m : ℤ) (y : UnitAddCircle), ‖fourier m y + (-1) ^ k * fourier (-m) y‖ ≤ 2 := by
    intro m y
    calc _ ≤ ‖fourier m y‖ + ‖(-1 : ℂ) ^ k * fourier (-m) y‖ := norm_add_le _ _
      _ = 2 := by
        rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, polybound_norm_fourier,
          polybound_norm_fourier]
        norm_num
  have hbound : ‖-(2 * (Real.pi : ℂ) * Complex.I) ^ k / (k.factorial : ℂ) * (bernoulliFun k x : ℂ)‖
      ≤ 2 * (Real.pi ^ 2 / 6) := by
    rw [← hs.tsum_eq]
    refine tsum_of_norm_bounded (hasSum_zeta_two.mul_left 2) fun n ↦ ?_
    rw [norm_mul]
    have h1 : ‖1 / (n : ℂ) ^ k‖ ≤ 1 / (n : ℝ) ^ 2 := by
      rw [norm_div, norm_one, norm_pow, Complex.norm_natCast]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [zero_pow (by omega : k ≠ 0)]
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hn1 hk)
    calc _ ≤ 1 / (n : ℝ) ^ 2 * 2 := mul_le_mul h1 (h2 _ _) (norm_nonneg _) (by positivity)
      _ = 2 * (1 / (n : ℝ) ^ 2) := mul_comm _ _
  have hnorm : ‖-(2 * (Real.pi : ℂ) * Complex.I) ^ k / (k.factorial : ℂ) * (bernoulliFun k x : ℂ)‖
      = (2 * Real.pi) ^ k / (k.factorial : ℝ) * |bernoulliFun k x| := by
    rw [norm_mul, norm_div, norm_neg, norm_pow, norm_mul, norm_mul, Complex.norm_I,
      Complex.norm_real, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one, Complex.norm_two]
  rw [← hnorm]
  refine hbound.trans ?_
  nlinarith [Real.pi_pos, Real.pi_lt_d2]

theorem UpperTheory.V.Bern.b_polybound :
    ∀ (k : ℕ) (x : ℚ), 0 ≤ x → x ≤ 1 → |(((Polynomial.bernoulli k).eval x : ℚ) : ℝ)| ≤ 4 * (k.factorial : ℝ) / (2 * Real.pi) ^ k := by
  intro k x h0 h1
  have hx0 : (0 : ℝ) ≤ x := by exact_mod_cast h0
  have hx1 : (x : ℝ) ≤ 1 := by exact_mod_cast h1
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  rcases lt_or_ge k 2 with hk | hk
  · interval_cases k
    · simp [Polynomial.bernoulli_zero]
    · simp only [Polynomial.bernoulli_one, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
        Nat.factorial_one, Nat.cast_one, pow_one]
      have key : |(x : ℝ) - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      have : (1 : ℝ) / 2 ≤ 4 * 1 / (2 * Real.pi) := by
        rw [le_div_iff₀ hpi]
        nlinarith [Real.pi_lt_d2]
      linarith
  · have hb := polybound_big hk (x := (x : ℝ)) ⟨hx0, hx1⟩
    rw [polybound_cast]
    have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    rw [div_mul_eq_mul_div, div_le_iff₀ hf] at hb
    rw [le_div_iff₀ (pow_pos hpi k)]
    linarith [mul_comm (|bernoulliFun k x|) ((2 * Real.pi) ^ k)]
end

section

open Finset UpperTheory.V.Bern

private theorem gauss_mul_gauss_inv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar * χ (-1) = N := by
  have hF : ZMod.dft (⇑χ) = fun k ↦ (fun j ↦ (⇑χ⁻¹) (-j)) k * gaussSum χ ZMod.stdAddChar :=
    funext fun k ↦ hχ.fourierTransform_eq_inv_mul_gaussSum k
  have h1 := congr_fun (ZMod.dft_dft (⇑χ)) 1
  rw [hF, ZMod.dft_mul_const, ZMod.dft_comp_neg] at h1
  simp only at h1
  rw [DirichletCharacter.fourierTransform_eq_gaussSum_mulShift, neg_neg, AddChar.mulShift_one,
    smul_eq_mul] at h1
  have hsq : χ (-1) * χ (-1) = 1 := by
    rw [← map_mul, neg_one_mul, neg_neg, map_one]
  rw [mul_comm (gaussSum χ _), h1, mul_assoc, hsq, mul_one]

private theorem conj_gauss {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    (starRingEnd ℂ) (gaussSum χ ZMod.stdAddChar) = gaussSum χ⁻¹ ZMod.stdAddChar * χ (-1) := by
  have h := gaussSum_mulShift_eq χ⁻¹ ZMod.stdAddChar (-1)
  rw [inv_inv, Units.val_neg, Units.val_one] at h
  rw [starRingEnd_apply, star_gaussSum_eq, AddChar.inv_mulShift, h, mul_comm]

theorem UpperTheory.V.Bern.b_gauss :
    ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt N ∧ ‖χ.rootNumber‖ = 1 := by
  intro N _ χ hχ
  have hns : (Complex.normSq (gaussSum χ ZMod.stdAddChar) : ℂ) = N := by
    rw [← Complex.mul_conj, conj_gauss, ← mul_assoc, gauss_mul_gauss_inv χ hχ]
  have hns' : Complex.normSq (gaussSum χ ZMod.stdAddChar) = N := by exact_mod_cast hns
  have hg : ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt N := by
    rw [Complex.norm_def, hns']
  refine ⟨hg, ?_⟩
  have hpos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  rw [DirichletCharacter.rootNumber, norm_div, norm_div, norm_pow, Complex.norm_I, one_pow, div_one,
    hg, Complex.norm_natCast_cpow_of_pos (NeZero.pos N)]
  rw [show (1 / 2 : ℂ).re = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  exact div_self (Real.sqrt_ne_zero'.mpr hpos)
end
