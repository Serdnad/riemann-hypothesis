module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Real.Pi.Bounds
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Monotonicity.Lemmas
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
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real

noncomputable section

namespace PGaussShell

theorem base_le (m δ : ℝ) (hm : 0 ≤ m) (hδ : 0 < δ) :
    1 + 2 * (m + 1) / δ ≤ 3 * (m + 1) * (1 + 1 / δ) := by
  have h2 : 3 * (m + 1) * (1 + 1 / δ) = 3 * (m + 1) + 3 * (m + 1) / δ := by ring
  have h1 : 2 * (m + 1) / δ ≤ 3 * (m + 1) / δ :=
    div_le_div_of_nonneg_right (by linarith) hδ.le
  linarith

end PGaussShell

theorem GaussShell.proof (hP : GaussPacking.Statement) (hT : GaussTermBound.Statement) :
    GaussShell.Statement := by
  intro n hn Λ δ hδ hmin F m
  set T := F.filter (fun μ : Λ => ⌊‖(μ : EuclideanSpace ℝ (Fin n))‖⌋₊ = m) with hTdef
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hlow : ∀ μ ∈ T, (m : ℝ) ≤ ‖(μ : EuclideanSpace ℝ (Fin n))‖ := by
    intro μ hμ
    rw [← (Finset.mem_filter.1 hμ).2]
    exact Nat.floor_le (norm_nonneg _)
  have hup : ∀ μ ∈ T, ‖(μ : EuclideanSpace ℝ (Fin n))‖ ≤ (m : ℝ) + 1 := by
    intro μ hμ
    have h := Nat.lt_floor_add_one ‖(μ : EuclideanSpace ℝ (Fin n))‖
    rw [(Finset.mem_filter.1 hμ).2] at h
    exact h.le
  have hterm : ∀ μ ∈ T, Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2) ≤
      Real.exp (-π * (m : ℝ) ^ 2) := by
    intro μ hμ
    apply Real.exp_le_exp.2
    have : (m : ℝ) ^ 2 ≤ ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2 :=
      pow_le_pow_left₀ hm0 (hlow μ hμ) 2
    nlinarith [Real.pi_pos]
  have hsum : ∑ μ ∈ T, Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2) ≤
      (T.card : ℝ) * Real.exp (-π * (m : ℝ) ^ 2) := by
    have h := Finset.sum_le_sum hterm
    rwa [Finset.sum_const, nsmul_eq_mul] at h
  have hcard : (T.card : ℝ) ≤ (1 + 2 * ((m : ℝ) + 1) / δ) ^ n := by
    have h := hP n (T.map (Function.Embedding.subtype _)) δ ((m : ℝ) + 1) hδ (by linarith) ?_ ?_
    · rwa [Finset.card_map] at h
    · intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.1 hy
      simp only [Function.Embedding.coe_subtype] at hxy ⊢
      exact hmin _ (Λ.sub_mem a.2 b.2) (sub_ne_zero.2 hxy)
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hx
      exact hup a ha
  have hδ' : (0 : ℝ) ≤ 1 + 1 / δ := by
    have : 0 ≤ 1 / δ := le_of_lt (one_div_pos.2 hδ)
    linarith
  have hb0 : (0 : ℝ) ≤ 1 + 2 * ((m : ℝ) + 1) / δ := by
    have : 0 ≤ 2 * ((m : ℝ) + 1) / δ := div_nonneg (by linarith) hδ.le
    linarith
  have hpow : (1 + 2 * ((m : ℝ) + 1) / δ) ^ n ≤
      3 ^ n * ((m : ℝ) + 1) ^ n * (1 + 1 / δ) ^ n := by
    rw [← mul_pow, ← mul_pow]
    exact pow_le_pow_left₀ hb0 (PGaussShell.base_le _ _ hm0 hδ) n
  calc ∑ μ ∈ T, Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2)
      ≤ (T.card : ℝ) * Real.exp (-π * (m : ℝ) ^ 2) := hsum
    _ ≤ 3 ^ n * ((m : ℝ) + 1) ^ n * (1 + 1 / δ) ^ n * Real.exp (-π * (m : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right (hcard.trans hpow) (Real.exp_pos _).le
    _ = 3 ^ n * (1 + 1 / δ) ^ n * (((m : ℝ) + 1) ^ n * Real.exp (-π * (m : ℝ) ^ 2)) := by ring
    _ ≤ 3 ^ n * (1 + 1 / δ) ^ n * (√(n : ℝ) ^ n * Real.exp √(n : ℝ) *
          Real.exp (n / (2 * π)) * Real.exp (-(m : ℝ))) :=
        mul_le_mul_of_nonneg_left (hT n hn m) (by positivity)
    _ = gaussShellConst n * (1 + 1 / δ) ^ n * Real.exp (-(m : ℝ)) := by
        unfold gaussShellConst; ring

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real

namespace PGaussTermBound

theorem pow_le_sqrt_pow_mul_exp (n m : ℕ) (hn : 1 ≤ n) :
    ((m : ℝ) + 1) ^ n ≤ √(n : ℝ) ^ n * Real.exp (√(n : ℝ) * ((m : ℝ) + 1)) := by
  set s := √(n : ℝ) with hs_def
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < s := Real.sqrt_pos.2 hn'
  have hss : s * s = n := Real.mul_self_sqrt hn'.le
  have hm : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  have h1 := Real.pow_div_factorial_le_exp (s * ((m : ℝ) + 1)) (mul_nonneg hs.le hm) n
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_iff₀ hfac] at h1
  have hfac2 : (n.factorial : ℝ) ≤ s ^ n * s ^ n := by
    rw [← mul_pow, hss]
    exact_mod_cast Nat.factorial_le_pow n
  have hE : 0 ≤ Real.exp (s * ((m : ℝ) + 1)) := (Real.exp_pos _).le
  have h2 : s ^ n * ((m : ℝ) + 1) ^ n ≤ s ^ n * (s ^ n * Real.exp (s * ((m : ℝ) + 1))) := by
    rw [← mul_pow]
    calc (s * ((m : ℝ) + 1)) ^ n ≤ Real.exp (s * ((m : ℝ) + 1)) * (n.factorial : ℝ) := h1
      _ ≤ Real.exp (s * ((m : ℝ) + 1)) * (s ^ n * s ^ n) := mul_le_mul_of_nonneg_left hfac2 hE
      _ = s ^ n * (s ^ n * Real.exp (s * ((m : ℝ) + 1))) := by ring
  exact le_of_mul_le_mul_left h2 (pow_pos hs n)

theorem exponent_le (n m : ℕ) :
    √(n : ℝ) * ((m : ℝ) + 1) + -π * (m : ℝ) ^ 2 ≤ √(n : ℝ) + n / (2 * π) + -(m : ℝ) := by
  set s := √(n : ℝ) with hs_def
  have hss : s * s = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hpi : 0 < π := Real.pi_pos
  have hpi3 : 3 < π := Real.pi_gt_three

  have hA : s * m - π / 2 * (m : ℝ) ^ 2 ≤ n / (2 * π) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (π * m - s)]

  have hB : (m : ℝ) ≤ π / 2 * (m : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h
      nlinarith
  nlinarith

end PGaussTermBound

theorem GaussTermBound.proof : GaussTermBound.Statement := by
  intro n hn m
  have h1 := PGaussTermBound.pow_le_sqrt_pow_mul_exp n m hn
  have h2 := PGaussTermBound.exponent_le n m
  have hE : 0 ≤ Real.exp (-π * (m : ℝ) ^ 2) := (Real.exp_pos _).le
  calc ((m : ℝ) + 1) ^ n * Real.exp (-π * (m : ℝ) ^ 2)
      ≤ √(n : ℝ) ^ n * Real.exp (√(n : ℝ) * ((m : ℝ) + 1)) * Real.exp (-π * (m : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right h1 hE
    _ = √(n : ℝ) ^ n * Real.exp (√(n : ℝ) * ((m : ℝ) + 1) + -π * (m : ℝ) ^ 2) := by
        rw [Real.exp_add]; ring
    _ ≤ √(n : ℝ) ^ n * Real.exp (√(n : ℝ) + n / (2 * π) + -(m : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h2) (by positivity)
    _ = √(n : ℝ) ^ n * Real.exp √(n : ℝ) * Real.exp (n / (2 * π)) * Real.exp (-(m : ℝ)) := by
        rw [Real.exp_add, Real.exp_add]; ring

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real

noncomputable section

namespace PGaussConstant

theorem rhs_eq (n : ℕ) :
    (72 * Real.exp 4 * (n : ℝ)) ^ ((n : ℝ) / 2) = (6 * √2 * Real.exp 2 * √(n : ℝ)) ^ n := by
  have hx : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have ha : 0 ≤ 6 * √2 * Real.exp 2 * √(n : ℝ) := by positivity
  have hsq : 72 * Real.exp 4 * (n : ℝ) = (6 * √2 * Real.exp 2 * √(n : ℝ)) ^ 2 := by
    have h4 : Real.exp 2 ^ 2 = Real.exp 4 := by
      rw [← Real.exp_nat_mul]; norm_num
    have : (6 * √2 * Real.exp 2 * √(n : ℝ)) ^ 2
        = 36 * (√2) ^ 2 * (Real.exp 2) ^ 2 * (√(n : ℝ)) ^ 2 := by ring
    rw [this, Real.sq_sqrt (by norm_num), Real.sq_sqrt hx, h4]
    ring
  rw [hsq, ← Real.rpow_natCast (6 * √2 * Real.exp 2 * √(n : ℝ)) 2, ← Real.rpow_mul ha,
    ← Real.rpow_natCast]
  congr 1
  push_cast
  ring

theorem exp_part (n : ℕ) (hn : 1 ≤ n) :
    2 * (Real.exp √(n : ℝ) * Real.exp ((n : ℝ) / (2 * π))) ≤ 2 ^ n * Real.exp 2 ^ n := by
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (2 : ℝ) ≤ 2 ^ n := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hs : √(n : ℝ) ≤ n := by
    have := Real.sqrt_le_sqrt (show (n : ℝ) ≤ (n : ℝ) ^ 2 by nlinarith)
    rwa [Real.sqrt_sq (by linarith)] at this
  have hpi : (n : ℝ) / (2 * π) ≤ n := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three]
  have he : Real.exp √(n : ℝ) * Real.exp ((n : ℝ) / (2 * π)) ≤ Real.exp 2 ^ n := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (by linarith)
  exact mul_le_mul h2 he (by positivity) (by positivity)

end PGaussConstant


open PGaussConstant in
theorem GaussConstant.proof : GaussConstant.Statement := by
  intro n hn
  rw [PGaussConstant.rhs_eq, gaussShellConst]
  have key := PGaussConstant.exp_part n hn
  have hc : 0 ≤ √2 ^ n * 3 ^ n * √(n : ℝ) ^ n := by positivity
  calc √2 ^ n * (2 * (3 ^ n * √(n : ℝ) ^ n * Real.exp √(n : ℝ) * Real.exp ((n : ℝ) / (2 * π))))
      = (√2 ^ n * 3 ^ n * √(n : ℝ) ^ n) *
          (2 * (Real.exp √(n : ℝ) * Real.exp ((n : ℝ) / (2 * π)))) := by ring
    _ ≤ (√2 ^ n * 3 ^ n * √(n : ℝ) ^ n) * (2 ^ n * Real.exp 2 ^ n) :=
        mul_le_mul_of_nonneg_left key hc
    _ = (6 * √2 * Real.exp 2 * √(n : ℝ)) ^ n := by
        rw [show (6 : ℝ) = 2 * 3 by norm_num]; simp only [mul_pow]; ring

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Real ComplexConjugate

noncomputable section

namespace KThetaCubeParseval

lemma torusChar_eq {g : ℕ} (m : Fin g → ℤ) (u : Fin g → ℝ) :
    torusChar m u = Complex.exp (((2 * π * ∑ i, (m i : ℝ) * u i : ℝ) : ℂ) * Complex.I) := by
  unfold torusChar
  congr 1
  push_cast
  ring

lemma norm_torusChar {g : ℕ} (m : Fin g → ℤ) (u : Fin g → ℝ) : ‖torusChar m u‖ = 1 := by
  rw [torusChar_eq, Complex.norm_exp_ofReal_mul_I]

lemma torusChar_mul_conj {g : ℕ} (k l : Fin g → ℤ) (u : Fin g → ℝ) :
    torusChar k u * conj (torusChar l u) = torusChar (k - l) u := by
  rw [torusChar_eq, torusChar_eq, torusChar_eq, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Pi.sub_apply, Int.cast_sub, sub_mul,
    Finset.sum_sub_distrib]
  push_cast
  ring

lemma continuous_torusChar {g : ℕ} (m : Fin g → ℤ) : Continuous (torusChar m) := by
  unfold torusChar
  fun_prop

lemma measureReal_cube (g : ℕ) :
    (volume.restrict (Set.Icc (0 : Fin g → ℝ) 1)).real Set.univ = 1 := by
  simp [Measure.real, Real.volume_Icc_pi]

end KThetaCubeParseval


open KThetaCubeParseval in
theorem ThetaCubeParseval.proof (h : ThetaCharIntegral.Statement) : ThetaCubeParseval.Statement := by
  intro g c hc
  set μ := volume.restrict (Set.Icc (0 : Fin g → ℝ) 1)

  set F : (Fin g → ℤ) × (Fin g → ℤ) → (Fin g → ℝ) → ℂ :=
    fun p u => c p.1 * conj (c p.2) * torusChar (p.1 - p.2) u with hF
  have hnorm1 : ∀ u, Summable fun k => ‖c k * torusChar k u‖ := fun u => by
    simpa [norm_torusChar] using hc
  have hnorm2 : ∀ u, Summable fun l => ‖conj (c l) * conj (torusChar l u)‖ := fun u => by
    simpa [norm_torusChar] using hc
  have hpt : ∀ u, ((‖∑' k, c k * torusChar k u‖ ^ 2 : ℝ) : ℂ) = ∑' p, F p u := by
    intro u
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, Complex.conj_tsum]
    simp only [map_mul]
    rw [tsum_mul_tsum_of_summable_norm (hnorm1 u) (hnorm2 u)]
    congr 1
    ext p
    rw [hF]
    dsimp only
    rw [← torusChar_mul_conj]
    ring
  have hnormF : ∀ p u, ‖F p u‖ = ‖c p.1‖ * ‖c p.2‖ := by
    intro p u
    simp [hF, norm_torusChar]
  have hint : ∀ p, Integrable (F p) μ := fun p =>
    ((continuous_torusChar (p.1 - p.2)).const_smul (c p.1 * conj (c p.2))).integrableOn_Icc
  have hμ : μ.real Set.univ = 1 := measureReal_cube g
  have hsum : Summable fun p => ∫ u, ‖F p u‖ ∂μ := by
    simp only [hnormF, integral_const, hμ, one_smul]
    exact Summable.mul_of_nonneg hc hc (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hterm : ∀ p, ∫ u, F p u ∂μ = if p.1 - p.2 = 0 then c p.1 * conj (c p.2) else 0 := by
    intro p
    rw [hF]
    dsimp only
    rw [integral_const_mul, h g (p.1 - p.2)]
    split_ifs <;> simp
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, Complex.ofReal_tsum]
  simp_rw [hpt]
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  simp_rw [hterm]
  have hinj : Function.Injective fun k : Fin g → ℤ => (k, k) := fun a b hab => (Prod.mk.inj hab).1
  rw [← hinj.tsum_eq]
  · congr 1
    ext k
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  · intro p hp
    have : p.1 - p.2 = 0 := by
      by_contra hne
      exact hp (by simp [hne])
    exact ⟨p.1, Prod.ext rfl (sub_eq_zero.mp this)⟩

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real

noncomputable section

namespace KThetaSummandNorm

lemma im_dot_period {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (w v : Fin g → ℝ) :
    ((fun i => (w i : ℂ)) ⬝ᵥ (periodMatrix X Y *ᵥ fun i => (v i : ℂ))).im = w ⬝ᵥ (Y *ᵥ v) := by
  simp only [dotProduct, mulVec, periodMatrix, Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_sum, Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply,
    smul_eq_mul, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.I_re, Complex.I_im]
  simp

lemma im_dot_real {g : ℕ} (w c : Fin g → ℝ) :
    ((fun i => (w i : ℂ)) ⬝ᵥ fun i => (c i : ℂ)).im = 0 := by
  simp [dotProduct, Complex.im_sum]

lemma qf_add {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.IsSymm) (w u : Fin g → ℝ) :
    qf Y (w + u) = qf Y w + 2 * (w ⬝ᵥ (Y *ᵥ u)) + qf Y u := by
  have h : u ⬝ᵥ (Y *ᵥ w) = w ⬝ᵥ (Y *ᵥ u) := by
    rw [dotProduct_mulVec, ← vecMul_transpose, hY.eq, dotProduct_comm]
  simp only [qf, mulVec_add, dotProduct_add, add_dotProduct, h]
  ring

end KThetaSummandNorm

open KThetaSummandNorm in
theorem ThetaSummandNorm.proof : ThetaSummandNorm.Statement := by
  intro g X Y a b u₁ u₂ k hY
  set w : Fin g → ℝ := intVec k + a with hw
  have hW : (fun i => ((intVec k i + a i : ℝ) : ℂ)) = fun i => (w i : ℂ) := rfl
  have hzb : (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ)) +
      (fun i => (b i : ℂ)) =
      periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => ((u₂ + b) i : ℂ) := by
    ext i; simp [add_assoc]
  have hre : (π * Complex.I *
      ((fun i => (w i : ℂ)) ⬝ᵥ (periodMatrix X Y *ᵥ fun i => (w i : ℂ))) +
      2 * π * Complex.I * ((fun i => (w i : ℂ)) ⬝ᵥ
        (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => ((u₂ + b) i : ℂ)))).re =
      -π * qf Y w - 2 * π * (w ⬝ᵥ (Y *ᵥ u₁)) := by
    rw [dotProduct_add]
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, Complex.add_im,
      im_dot_period, im_dot_real]
    simp only [qf]
    ring
  unfold thetaSummand
  rw [hW, hzb, Complex.norm_exp, hre, ← Real.exp_add]
  congr 1
  have : intVec k + a + u₁ = w + u₁ := rfl
  rw [this, qf_add Y hY w u₁]
  ring

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real

theorem GaussianSum.proof (hPD : GaussPoissonDual.Statement) (hSS : GaussShellSum.Statement)
    (hC : GaussConstant.Statement) : GaussianSum.Statement := by
  refine ⟨72 * Real.exp 4, by positivity, ?_⟩
  intro g Y ρ hY hρ hmin u
  obtain ⟨hsum, Λ, hΛ, hle⟩ := hPD g Y ρ hY hρ hmin u
  refine ⟨hsum, ?_⟩
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · have hq : ∀ k : Fin 0 → ℤ, qf Y (intVec k + u) = 0 := fun k => by simp [qf]
    simp only [hq, mul_zero, Real.exp_zero, tsum_const, Nat.card_unique, one_smul,
      Nat.cast_zero, zero_div, Real.rpow_zero, Matrix.det_isEmpty, Real.one_rpow, pow_zero,
      mul_one, le_refl]
  · have hdet : 0 < Y.det := hY.det_pos
    have hd : 0 ≤ Y.det ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hdet.le _
    have hS := (hSS g hg Λ ρ hρ hΛ).2
    have hc := hC g hg
    have hr : 0 ≤ (1 + 1 / ρ) ^ g := by positivity
    calc ∑' k : Fin g → ℤ, Real.exp (-(π / 2) * qf Y (intVec k + u))
        ≤ √2 ^ g * Y.det ^ (-(1 / 2 : ℝ)) *
            ∑' μ : Λ, Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin g))‖ ^ 2) := hle
      _ ≤ √2 ^ g * Y.det ^ (-(1 / 2 : ℝ)) * (2 * gaussShellConst g * (1 + 1 / ρ) ^ g) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ = √2 ^ g * (2 * gaussShellConst g) * Y.det ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g := by ring
      _ ≤ (72 * Real.exp 4 * g) ^ ((g : ℝ) / 2) * Y.det ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hd) hr

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def ChartDensityIntegrable.Statement : Prop :=
  ∀ (e : ℕ) (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ), M.PosDef →
    Integrable (fun y : Fin e → ℂ => maDensity (fun _ : Fin e => hermChartPot M) y)

end

end GroundTheory.Heights₂.Heights
end
