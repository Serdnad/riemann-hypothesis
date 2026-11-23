module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle012
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle019
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle016
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle020
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle015

@[expose] public section

section

noncomputable section

open Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalcCH

open DCalcH DCalcBH

variable {m n : ℕ}

theorem mR_one : mR (1 : GR n) = 1 := rfl

theorem cnt_add (ε : Fin m → Bool) : cnt ε true + cnt ε false = m := by
  unfold cnt
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  have h : ∀ a : Fin m, ((if ε a = true then 1 else 0) + (if ε a = false then 1 else 0) : ℕ) = 1 := by
    intro a; cases ε a <;> simp
  simp [h]

theorem det_diag_exp (X : Fin n → ℝ) (z : ℂ) :
    (diagonal fun j => Complex.exp (-(z * X j))).det = Complex.exp (-(z * ∑ j, (X j : ℂ))) := by
  rw [det_diagonal, ← Complex.exp_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]

theorem det_aC (X : Fin n → ℝ) (z : ℂ) : (aC X z).det = 1 := by
  unfold aC
  rw [det_fromBlocks_zero₂₁, det_diagonal, det_diagonal, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

theorem zpow_exp_neg (w : ℂ) (p : ℕ) : Complex.exp (-w) ^ (-(p : ℤ)) = Complex.exp ((p : ℂ) * w) := by
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem jC_one (e : ℤ) (p q : ℕ) (X : Fin n → ℝ) (z : ℂ) :
    jC e p q 1 X z = Complex.exp (((p : ℂ) + q) * (z * ∑ j, (X j : ℂ))) := by
  unfold jC
  simp only [mR_one, Matrix.one_mul]
  rw [det_aC]
  unfold aC
  simp only [toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add, _root_.one_zpow, one_mul]
  rw [det_diag_exp, zpow_exp_neg, zpow_exp_neg, ← Complex.exp_add]
  congr 1
  ring

theorem inv_diag_exp (X : Fin n → ℝ) (z : ℂ) :
    (diagonal fun j => Complex.exp (-(z * X j)))⁻¹ = diagonal fun j => Complex.exp (z * X j) := by
  refine Matrix.inv_eq_left_inv ?_
  rw [diagonal_mul_diagonal]
  conv_rhs => rw [← diagonal_one]
  congr 1
  funext j
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

theorem ptZ_one (X : Fin n → ℝ) (z s₀ : ℂ) :
    ptZ 1 X z s₀ = s₀ • diagonal fun j => Complex.exp (2 * z * X j) := by
  unfold ptZ
  simp only [mR_one, Matrix.one_mul]
  unfold aC
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.zero_mul, zero_add, add_zero]
  rw [inv_diag_exp, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, diagonal_mul_diagonal]
  congr 2
  funext j
  rw [← Complex.exp_add]
  congr 1
  ring

theorem gramB_diag (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) (j : Fin n) :
    gramB ε b u j j = ∑ a ∈ Finset.univ.filter (fun a => ε a = b), star (u a j) * u a j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [gramB, Qb, evX, map_sum, eval_X]

theorem trace_sdiag (s₀ : ℂ) (w : Fin n → ℂ) (G : Matrix (Fin n) (Fin n) ℂ) :
    ((s₀ • diagonal w) * G).trace = s₀ * ∑ j, w j * G j j := by
  rw [Matrix.smul_mul, trace_smul, smul_eq_mul]
  congr 1
  simp [trace, diagonal_mul]

theorem famC_one (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (X : Fin n → ℝ) (u : Fin m → Fin n → ℂ) (s : ℝ) :
    famC ε t c e 1 X (s : ℂ) u = fF c X 1 u s := by
  unfold famC fF fP
  rw [jC_one, ptZ_one, ptZ_one, gs_vS]
  unfold gC
  rw [trace_sdiag, trace_sdiag]
  simp only [gramB_diag, evX_eq, map_one, one_mul]
  have hpq : ((cnt (epsT t ε) true : ℂ) + (cnt (epsT t ε) false : ℂ)) = (m : ℂ) := by
    rw [← Nat.cast_add, cnt_add]
  rw [hpq, ← Complex.exp_add, Complex.ofReal_exp]
  have hsum : ∀ j, (∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = true), star (u a j) * u a j) +
      (∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = false), star (u a j) * u a j) =
      ∑ a, ((‖u a j‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    have := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin m)))
      (p := fun a => epsT t ε a = true) (f := fun a => star (u a j) * u a j)
    simp only [Bool.not_eq_true] at this
    rw [this]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
    push_cast; ring
  have e2 : ∀ j, Complex.exp (2 * (s : ℂ) * (X j : ℂ)) = ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) := by
    intro j
    push_cast
    rw [← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  unfold nS
  push_cast
  simp only [e2]
  have key : Complex.I * (c : ℂ) * (Complex.I * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) *
        ∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = true), star (u a j) * u a j) -
      Complex.I * (c : ℂ) * (-Complex.I * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) *
        ∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = false), star (u a j) * u a j) =
      -((c : ℂ) * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) * ∑ a, ((‖u a j‖ ^ 2 : ℝ) : ℂ)) := by
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    simp only [← hsum, mul_add, Finset.sum_add_distrib]
    linear_combination ((c : ℂ) * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) *
        ∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = true), star (u a j) * u a j +
      (c : ℂ) * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) *
        ∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = false), star (u a j) * u a j) * hI
  rw [key, ← Complex.exp_add]
  have hswap : ∀ (E : Fin n → ℂ) (N : Fin m → Fin n → ℂ), (∑ j, E j * ∑ a, N a j) = ∑ a, ∑ j, N a j * E j := by
    intro E N
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
  congr 1
  push_cast
  rw [hswap]
  ring

end DCalcCH

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open MeasureTheory Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalc2H

open DCalcH DCalcBH DCalcDH DCalcEH

variable {m n : ℕ}

theorem hasDeriv (c : ℝ) (X : Fin n → ℝ) (P : PX m n) (u : Fin m → Fin n → ℂ) (t : ℝ) :
    HasDerivAt (fun t => fF c X P u t) (fF c X (dil c X P) u t) t :=
  fF_hasDeriv c X P u t

theorem quot_le (c : ℝ) (X : Fin n → ℝ) (P : PX m n) (u : Fin m → Fin n → ℂ) (s B : ℝ)
    (hB : ∀ t ∈ Set.Icc (s - 1) (s + 1), ‖fF c X (dil c X P) u t‖ ≤ B) (h : ℝ) (hh : |h| ≤ 1) :
    ‖fF c X P u (s + h) - fF c X P u s‖ ≤ B * |h| := by
  have hcv : Convex ℝ (Set.Icc (s - 1) (s + 1)) := convex_Icc _ _
  have hs : s ∈ Set.Icc (s - 1) (s + 1) := ⟨by linarith, by linarith⟩
  have hsh : s + h ∈ Set.Icc (s - 1) (s + 1) := by
    rw [abs_le] at hh; exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have := hcv.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun t => fF c X P u t)
    (fun t _ => (hasDeriv c X P u t).hasDerivWithinAt) hB hs hsh
  simpa [Real.norm_eq_abs] using this

theorem l2conv (c : ℝ) (hc : 0 < c) (X : Fin n → ℝ) (P : PX m n) (s : ℝ) :
    Tendsto (fun h : ℝ => ∫ u, ‖(fF c X P u (s + h) - fF c X P u s) / (h : ℂ) - fF c X (dil c X P) u s‖ ^ 2)
      (𝓝[≠] 0) (𝓝 0) := by
  obtain ⟨K, a, hK, ha, hb⟩ := fF_bound c hc X (dil c X P) s
  suffices key : Tendsto (fun h : ℝ => ∫ u, ‖(fF c X P u (s + h) - fF c X P u s) / (h : ℂ) - fF c X (dil c X P) u s‖ ^ 2)
      (𝓝[≠] 0) (𝓝 (∫ _u : Fin m → Fin n → ℂ, (0 : ℝ))) by simpa using key
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u => (2 * K) ^ 2 * Real.exp (-(2 * a * sqN u))) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun h => ?_
    refine Continuous.aestronglyMeasurable ?_
    have h1 := fF_cont c X P (s + h)
    have h2 := fF_cont c X P s
    have h3 := fF_cont c X (dil c X P) s
    fun_prop
  · have hev : ∀ᶠ h in 𝓝[≠] (0 : ℝ), |h| ≤ 1 ∧ h ≠ 0 := by
      refine (eventually_nhdsWithin_of_eventually_nhds ?_).and self_mem_nhdsWithin
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with h hh
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hh
      exact hh.le
    filter_upwards [hev] with h ⟨hh, h0⟩
    refine Eventually.of_forall fun u => ?_
    have hB : ∀ t ∈ Set.Icc (s - 1) (s + 1), ‖fF c X (dil c X P) u t‖ ≤ K * Real.exp (-(a * sqN u)) := fun t ht => hb u t ht
    have hq := quot_le c X P u s _ hB h hh
    have hhpos : 0 < |h| := abs_pos.2 h0
    have e1 : ‖(fF c X P u (s + h) - fF c X P u s) / (h : ℂ)‖ ≤ K * Real.exp (-(a * sqN u)) := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ hhpos]
      exact hq
    have e2 : ‖fF c X (dil c X P) u s‖ ≤ K * Real.exp (-(a * sqN u)) := hb u s ⟨by linarith, by linarith⟩
    have e3 : ‖(fF c X P u (s + h) - fF c X P u s) / (h : ℂ) - fF c X (dil c X P) u s‖ ≤ 2 * K * Real.exp (-(a * sqN u)) := by
      calc _ ≤ ‖(fF c X P u (s + h) - fF c X P u s) / (h : ℂ)‖ + ‖fF c X (dil c X P) u s‖ := norm_sub_le _ _
        _ ≤ _ := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖(fF c X P u (s + h) - fF c X P u s) / (h : ℂ) - fF c X (dil c X P) u s‖ ^ 2
        ≤ (2 * K * Real.exp (-(a * sqN u))) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) e3 2
      _ = (2 * K) ^ 2 * Real.exp (-(2 * a * sqN u)) := by
        rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
  · exact (integrable_gauss (2 * a) (by positivity)).const_mul _
  · refine Eventually.of_forall fun u => ?_
    have : Tendsto (fun h : ℝ => (fF c X P u (s + h) - fF c X P u s) / (h : ℂ) - fF c X (dil c X P) u s) (𝓝[≠] 0) (𝓝 0) := by
      have h2 := (hasDeriv c X P u s).tendsto_slope_zero
      have h3 := h2.sub_const (fF c X (dil c X P) u s)
      rw [sub_self] at h3
      refine h3.congr' (Eventually.of_forall fun h => ?_)
      show h⁻¹ • (fF c X P u (s + h) - fF c X P u s) - fF c X (dil c X P) u s =
        (fF c X P u (s + h) - fF c X P u s) / (h : ℂ) - fF c X (dil c X P) u s
      rw [Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul]
    have := (this.norm).pow 2
    simpa using this

end DCalc2H

end PositivityTheory.Rg.Sw.Glob

end
end

section

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

theorem eq_zero_of_siegel {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSiegel Z) {v : Fin n → ℂ}
    (h : star v ⬝ᵥ ((Z - Zᴴ) *ᵥ v) = 0) : v = 0 := by
  by_contra hv
  have hpos := Matrix.PosDef.dotProduct_mulVec_pos hZ hv
  rw [smul_mulVec, dotProduct_smul, h, smul_zero] at hpos
  exact lt_irrefl _ hpos

theorem det_CZhD {g : M2 n} (hg : InG g) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSiegel Z) :
    IsUnit (g.toBlocks₂₁ * Zᴴ + g.toBlocks₂₂).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hid := identG hg Zᴴ Zᴴ
  rw [conjTranspose_conjTranspose] at hid
  have h0 : star v ⬝ᵥ ((Z - Zᴴ) *ᵥ v) = 0 := by
    rw [← hid, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hMv, mulVec_zero, dotProduct_sub,
      dotProduct_zero, dotProduct_mulVec, ← star_mulVec, hMv]
    simp
  exact hv (eq_zero_of_siegel hZ h0)

theorem isSiegel_I : IsSiegel (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  unfold IsSiegel
  have hs : -(Complex.I / 2) * (Complex.I - star Complex.I) = 1 := by
    rw [Complex.star_def, Complex.conj_I]
    linear_combination (-1 : ℂ) * Complex.I_sq
  rw [conjTranspose_smul, conjTranspose_one, ← sub_smul, smul_smul, hs, one_smul]
  exact Matrix.PosDef.one

theorem toBlocks₁₁_mul (M N : M2 n) : (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ + M.toBlocks₁₂ * N.toBlocks₂₁ := by
  have := congrArg toBlocks₁₁ (fromBlocks_multiply M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁
    M.toBlocks₂₂ N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂)
  simpa only [fromBlocks_toBlocks, toBlocks_fromBlocks₁₁] using this

theorem toBlocks₁₂_mul (M N : M2 n) : (M * N).toBlocks₁₂ = M.toBlocks₁₁ * N.toBlocks₁₂ + M.toBlocks₁₂ * N.toBlocks₂₂ := by
  have := congrArg toBlocks₁₂ (fromBlocks_multiply M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁
    M.toBlocks₂₂ N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂)
  simpa only [fromBlocks_toBlocks, toBlocks_fromBlocks₁₂] using this

theorem toBlocks₂₁_mul (M N : M2 n) : (M * N).toBlocks₂₁ = M.toBlocks₂₁ * N.toBlocks₁₁ + M.toBlocks₂₂ * N.toBlocks₂₁ := by
  have := congrArg toBlocks₂₁ (fromBlocks_multiply M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁
    M.toBlocks₂₂ N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂)
  simpa only [fromBlocks_toBlocks, toBlocks_fromBlocks₂₁] using this

theorem toBlocks₂₂_mul (M N : M2 n) : (M * N).toBlocks₂₂ = M.toBlocks₂₁ * N.toBlocks₁₂ + M.toBlocks₂₂ * N.toBlocks₂₂ := by
  have := congrArg toBlocks₂₂ (fromBlocks_multiply M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁
    M.toBlocks₂₂ N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂)
  simpa only [fromBlocks_toBlocks, toBlocks_fromBlocks₂₂] using this

theorem mR_mul (y y' : GR n) : mR (y * y') = mR y * mR y' := rfl

theorem inG_mR (y : GR n) : InG (mR y) := y.2

theorem num_den_mul (M N : M2 n) (Z W : Matrix (Fin n) (Fin n) ℂ)
    (hW : W * (N.toBlocks₂₁ * Z + N.toBlocks₂₂) = N.toBlocks₁₁ * Z + N.toBlocks₁₂) :
    (M * N).toBlocks₁₁ * Z + (M * N).toBlocks₁₂ = (M.toBlocks₁₁ * W + M.toBlocks₁₂) * (N.toBlocks₂₁ * Z + N.toBlocks₂₂) ∧
    (M * N).toBlocks₂₁ * Z + (M * N).toBlocks₂₂ = (M.toBlocks₂₁ * W + M.toBlocks₂₂) * (N.toBlocks₂₁ * Z + N.toBlocks₂₂) := by
  rw [toBlocks₁₁_mul, toBlocks₁₂_mul, toBlocks₂₁_mul, toBlocks₂₂_mul]
  constructor
  · have e : (M.toBlocks₁₁ * W + M.toBlocks₁₂) * (N.toBlocks₂₁ * Z + N.toBlocks₂₂) =
        M.toBlocks₁₁ * (W * (N.toBlocks₂₁ * Z + N.toBlocks₂₂)) +
          M.toBlocks₁₂ * (N.toBlocks₂₁ * Z + N.toBlocks₂₂) := by noncomm_ring
    rw [e, hW]
    noncomm_ring
  · have e : (M.toBlocks₂₁ * W + M.toBlocks₂₂) * (N.toBlocks₂₁ * Z + N.toBlocks₂₂) =
        M.toBlocks₂₁ * (W * (N.toBlocks₂₁ * Z + N.toBlocks₂₂)) +
          M.toBlocks₂₂ * (N.toBlocks₂₁ * Z + N.toBlocks₂₂) := by noncomm_ring
    rw [e, hW]
    noncomm_ring

end PositivityTheory.Rg.Sw.Glob.GaussH
end
end

section

noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.Glob

namespace SchwartzDifferenceQuotient

variable {m n : ℕ}

instance haarInner (n : ℕ) : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _

instance haarOuter (m n : ℕ) : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _

theorem isSch_sub {f g : (Fin m → Fin n → ℂ) → ℂ} (hf : IsSch f) (hg : IsSch g) : IsSch (f - g) := by
  obtain ⟨S, rfl⟩ := hf
  obtain ⟨S', rfl⟩ := hg
  exact ⟨S - S', by ext u; simp⟩

theorem isSch_smul (a : ℂ) {f : (Fin m → Fin n → ℂ) → ℂ} (hf : IsSch f) : IsSch (fun u => a * f u) := by
  obtain ⟨S, rfl⟩ := hf
  exact ⟨a • S, by ext u; simp [smul_eq_mul]⟩

theorem isSch_continuous {f : (Fin m → Fin n → ℂ) → ℂ} (hf : IsSch f) : Continuous f := by
  obtain ⟨S, rfl⟩ := hf
  exact S.continuous

theorem isSch_sq_integrable {f : (Fin m → Fin n → ℂ) → ℂ} (hf : IsSch f) :
    Integrable (fun u => ‖f u‖ ^ 2) := by
  obtain ⟨S, rfl⟩ := hf
  exact (S.memLp ((2 : ℕ) : ENNReal) volume).integrable_norm_pow two_ne_zero

end SchwartzDifferenceQuotient

open SchwartzDifferenceQuotient in
theorem dL2 : DifferenceQuotientIsometryExchange := by
  intro m n T κ hκ hTS hTsub hTsmul hTiso G G' E' s hG hG' hE' hL2 hpt
  have hD : ∀ h : ℝ, IsSch (fun u => (G (s + h) u - G s u) / (h : ℂ) - G' u) := by
    intro h
    have h3 := isSch_sub (isSch_smul ((h : ℂ)⁻¹) (isSch_sub (hG (s + h)) (hG s))) hG'
    convert h3 using 1
    funext u
    simp only [Pi.sub_apply, div_eq_mul_inv]
    ring
  have hTD : ∀ h : ℝ, T (fun u => (G (s + h) u - G s u) / (h : ℂ) - G' u) =
      fun u => (T (G (s + h)) u - T (G s) u) / (h : ℂ) - T G' u := by
    intro h
    have e1 : (fun u => (G (s + h) u - G s u) / (h : ℂ) - G' u) =
        (fun u => (h : ℂ)⁻¹ * (G (s + h) - G s) u) - G' := by
      funext u
      simp only [Pi.sub_apply]
      try ring
    rw [e1, hTsub _ _ (isSch_smul _ (isSch_sub (hG _) (hG _))) hG',
      hTsmul _ _ (isSch_sub (hG _) (hG _)), hTsub _ _ (hG _) (hG _)]
    funext u
    simp only [Pi.sub_apply]
    try ring
  obtain ⟨F, hF⟩ : ∃ F : ℝ → (Fin m → Fin n → ℂ) → ENNReal,
      F = fun h u => ENNReal.ofReal (‖(T (G (s + h)) u - T (G s) u) / (h : ℂ) - T G' u‖ ^ 2) := ⟨_, rfl⟩
  have hmeas : ∀ h, Measurable (F h) := by
    intro h
    have hc := isSch_continuous (hTS _ (hD h))
    rw [hTD] at hc
    rw [hF]
    exact ENNReal.measurable_ofReal.comp (hc.norm.pow 2).measurable
  have hlim_pt : ∀ u, Tendsto (fun h => F h u) (𝓝[≠] 0) (𝓝 (ENNReal.ofReal (‖E' u - T G' u‖ ^ 2))) := by
    intro u
    rw [hF]
    have h1 := ((hpt u).sub_const (T G' u)).norm.pow 2
    exact (ENNReal.continuous_ofReal.tendsto _).comp h1
  have hint : ∀ h, ∫⁻ u, F h u = ENNReal.ofReal (κ * ∫ u, ‖(G (s + h) u - G s u) / (h : ℂ) - G' u‖ ^ 2) := by
    intro h
    rw [← hTiso _ (hD h), hTD, ofReal_integral_eq_lintegral_ofReal, hF]
    · have hi := isSch_sq_integrable (hTS _ (hD h))
      rw [hTD] at hi
      exact hi
    · exact Filter.Eventually.of_forall fun u => sq_nonneg _
  have hlim_int : Tendsto (fun h => ∫⁻ u, F h u) (𝓝[≠] 0) (𝓝 0) := by
    simp_rw [hint]
    have h1 := hL2.const_mul κ
    rw [mul_zero] at h1
    have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h1
    rw [ENNReal.ofReal_zero] at h2
    exact h2
  have hfatou := lintegral_liminf_le (μ := (volume : Measure (Fin m → Fin n → ℂ))) (u := 𝓝[≠] (0 : ℝ)) hmeas
  rw [hlim_int.liminf_eq] at hfatou
  have hz : ∫⁻ u, ENNReal.ofReal (‖E' u - T G' u‖ ^ 2) = 0 := by
    refine le_antisymm ?_ (by simp)
    calc _ = ∫⁻ u, liminf (fun h => F h u) (𝓝[≠] (0 : ℝ)) := by
          congr 1
          funext u
          exact ((hlim_pt u).liminf_eq).symm
      _ ≤ 0 := hfatou
  have hcT := isSch_continuous (hTS _ hG')
  have hcE : Continuous fun u => E' u - T G' u := hE'.sub hcT
  have hm : Measurable fun u => ENNReal.ofReal (‖E' u - T G' u‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp (hcE.norm.pow 2).measurable
  rw [lintegral_eq_zero_iff hm] at hz
  have hae : E' =ᵐ[volume] T G' := by
    filter_upwards [hz] with u hu
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hu
    exact sub_eq_zero.mp (norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp (le_antisymm hu (sq_nonneg _))))
  exact ((Continuous.ae_eq_iff_eq volume hE' hcT).mp hae).symm

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

def PlanchLoc : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (t : ℝ), t ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∀ f : (Fin m → Fin n → ℂ) → ℂ, IsSch f →
    ∫ u, ‖ftLoc ε t f u‖ ^ 2 = c * ∫ u, ‖f u‖ ^ 2

def AwayNZ : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι →
    ∃ (Ψ : Mx D V.rank n → ℂ) (x₀ : Mx D V.rank n), AwayCls θ τ fr Ψ ∧ Ψ x₀ ≠ 0

end PositivityTheory.Rg.Sw.Glob
end
end
