module

public import ReciprocityTheory.SemistableReduction.Bundle002
public import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement
public import ReciprocityTheory.SemistableReduction.Bundle006
public import ReciprocityTheory.SemistableReduction.Bundle007
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
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import ReciprocityTheory.SemistableReduction.Bundle003
public import ReciprocityTheory.SemistableReduction.Bundle005
public import ReciprocityTheory.SemistableReduction.Bundle012

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Polynomial

theorem bwPoly_holds (hH : LemmaHStatement) (hE : ∀ n, ReciprocityTheory.L2DbarEstimates.EXTStatement n)
    (hO : OnePolyGrowthStatement) : BWPolyStatement := by
  intro p a P hP hT
  obtain ⟨F, hF⟩ := bwp_ext_poly (σ := Fin p × Fin p) (∑ i, a i) (fun z => P (bwpMat z))
    (fun z => (bwpMat z).det) (bwpId p) (fun z => bwp_finite_det_id_line z)
    (fun z v hz => bwp_finite_det_line z v hz) (fun z v hB => bwp_line_poly hH hO a P hP hT z v hB)
  have hF' : ∀ z, (bwpMat z).det ≠ 0 → P (bwpMat z) = MvPolynomial.eval z F := fun z hz => hF z hz
  refine ⟨MvPolynomial.homogeneousComponent (∑ i, a i) F,
    MvPolynomial.homogeneousComponent_isHomogeneous _ _, fun x hx => ?_⟩
  set z : Fin p × Fin p → ℂ := fun ij => x ij.1 ij.2 with hz
  have hxz : bwpMat z = x := by
    ext i j
    rfl
  have hPz : P x = MvPolynomial.eval z F := by
    rw [← hxz]
    exact hF' z (by rw [hxz]; exact hx)
  rw [hPz]
  have hscale : ∀ t : ℂ, t ≠ 0 → MvPolynomial.eval (t • z) F = t ^ (∑ i, a i) * MvPolynomial.eval z F := by
    intro t ht
    have hb : bwpMat (t • z) = x * (t • (1 : Matrix (Fin p) (Fin p) ℂ)) := by
      ext i j
      simp [bwpMat, hz, Matrix.mul_smul]
    have hbdet : (t • (1 : Matrix (Fin p) (Fin p) ℂ)).det ≠ 0 := by
      rw [Matrix.det_smul, Matrix.det_one, mul_one]
      exact pow_ne_zero _ ht
    have hbtri : (t • (1 : Matrix (Fin p) (Fin p) ℂ)).BlockTriangular id := by
      intro i j h
      have hij : i ≠ j := fun hij => by subst hij; exact lt_irrefl _ h
      rw [Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero]
    have hdet : (bwpMat (t • z)).det ≠ 0 := by
      rw [hb, Matrix.det_mul]
      exact mul_ne_zero hx hbdet
    rw [← hF' _ hdet, hb, hT x _ hx hbdet hbtri, hPz]
    congr 1
    simp [triChar, Finset.prod_pow_eq_pow_sum]
  have hsum : ∀ t : ℂ, MvPolynomial.eval (t • z) F = ∑ j ∈ Finset.range (F.totalDegree + 1),
      t ^ j * MvPolynomial.eval z (MvPolynomial.homogeneousComponent j F) := by
    intro t
    conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent F]

    rw [map_sum]
    exact Finset.sum_congr rfl (fun j _ => bwp_eval_smul_of_isHomogeneous
      (MvPolynomial.homogeneousComponent_isHomogeneous j F) t z)
  have hΦ : (∑ j ∈ Finset.range (F.totalDegree + 1),
      Polynomial.C (MvPolynomial.eval z (MvPolynomial.homogeneousComponent j F)) * Polynomial.X ^ j) =
      Polynomial.C (MvPolynomial.eval z F) * Polynomial.X ^ (∑ i, a i) := by
    refine bwp_poly_eq_of_eval_eq_off _ _ {0} (Set.finite_singleton 0) (fun t ht => ?_)
    have ht0 : t ≠ 0 := ht
    rw [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, mul_comm, ← hscale t ht0, hsum t]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_comm]
  have hc := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q (∑ i, a i)) hΦ
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, if_pos rfl] at hc
  rw [Finset.sum_ite_eq] at hc
  split_ifs at hc with hk
  · exact hc.symm
  · rw [MvPolynomial.homogeneousComponent_eq_zero _ _ (by simpa using hk), map_zero]
    exact hc.symm

end ReciprocityTheory.MultiplicativeHeights
end
end

section

namespace ReciprocityTheory.MultiplicativeHeights.TorusLexOrder

open MeasureTheory ComplexConjugate

private theorem norm_torusMono_eq_one {ι : Type} [Fintype ι] (θ : ι → ℝ) (s : ι →₀ ℕ) :
    ‖torusMono θ s‖ = 1 := by
  unfold torusMono
  rw [norm_prod]
  simp [norm_pow, norm_torusPoint]

private theorem continuous_torusMono' {ι : Type} [Fintype ι] (s : ι →₀ ℕ) :
    Continuous (fun θ : ι → ℝ => torusMono θ s) := by
  have h : ∀ i, Continuous fun θ : ι → ℝ => torusPoint θ i :=
    fun i => (continuous_apply i).comp continuous_torusPoint
  unfold torusMono
  exact continuous_finsetProd _ (fun i _ => (h i).pow _)

theorem integrable_torus_term {ι : Type} [Fintype ι] (f : MvPolynomial ι ℂ) (s : ι →₀ ℕ) :
    Integrable (fun θ => MvPolynomial.eval (torusPoint θ) f * conj (torusMono θ s))
      (torusProb ι) := by
  refine integrable_of_bdd ((continuous_eval_torus f).mul
    (Complex.continuous_conj.comp (continuous_torusMono' s))) (∑ t ∈ f.support, ‖f.coeff t‖)
    (fun θ => ?_)
  have h := norm_eval_torus_le f θ
  simpa [norm_torusMono_eq_one] using h

theorem integrable_mono_term {ι : Type} [Fintype ι] (t s : ι →₀ ℕ) :
    Integrable (fun θ => torusMono θ t * conj (torusMono θ s)) (torusProb ι) := by
  refine integrable_of_bdd ((continuous_torusMono' t).mul
    (Complex.continuous_conj.comp (continuous_torusMono' s))) 1 (fun θ => ?_)
  simp [norm_torusMono_eq_one]

theorem torus_coeff_integral {ι : Type} [Fintype ι] (f : MvPolynomial ι ℂ) (s : ι →₀ ℕ) :
    ∫ θ, MvPolynomial.eval (torusPoint θ) f * conj (torusMono θ s) ∂(torusProb ι) =
      f.coeff s := by
  simp_rw [eval_torus, Finset.sum_mul]
  rw [MeasureTheory.integral_finsetSum _ (fun t _ => by
    simpa [mul_assoc] using (integrable_mono_term t s).const_mul (f.coeff t))]
  simp_rw [mul_assoc, integral_const_mul, torus_orth, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (MvPolynomial.notMem_support_iff.mp h).symm

theorem torus_parseval {ι : Type} [Fintype ι] (f : MvPolynomial ι ℂ) :
    ∫ θ, ‖MvPolynomial.eval (torusPoint θ) f‖ ^ 2 ∂(torusProb ι) =
      ∑ s ∈ f.support, ‖f.coeff s‖ ^ 2 := by
  have key : ∀ θ, ((‖MvPolynomial.eval (torusPoint θ) f‖ ^ 2 : ℝ) : ℂ) =
      ∑ s ∈ f.support, conj (f.coeff s) *
        (MvPolynomial.eval (torusPoint θ) f * conj (torusMono θ s)) := by
    intro θ
    have hc : conj (MvPolynomial.eval (torusPoint θ) f) =
        ∑ s ∈ f.support, conj (f.coeff s) * conj (torusMono θ s) := by
      conv_lhs => rw [eval_torus]

      simp [map_sum, map_mul]
    push_cast
    rw [show ((‖MvPolynomial.eval (torusPoint θ) f‖ : ℂ)) ^ 2 =
        MvPolynomial.eval (torusPoint θ) f * conj (MvPolynomial.eval (torusPoint θ) f) by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring]
    rw [hc, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    ring
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [key]
  rw [MeasureTheory.integral_finsetSum _ (fun s _ => (integrable_torus_term f s).const_mul _)]
  simp_rw [integral_const_mul, torus_coeff_integral]
  push_cast
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem torusPoint_fract {ι : Type} (θ : ι → ℝ) :
    torusPoint (fun i => Int.fract (θ i)) = torusPoint θ := by
  funext i
  simp only [torusPoint]
  rw [← Int.self_sub_floor]
  push_cast
  rw [mul_sub, Complex.exp_sub]
  have h : Complex.exp (2 * Real.pi * Complex.I * ((⌊θ i⌋ : ℤ) : ℂ)) = 1 := by
    rw [show 2 * Real.pi * Complex.I * ((⌊θ i⌋ : ℤ) : ℂ) = (⌊θ i⌋ : ℤ) * (2 * Real.pi * Complex.I) by
      ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [h, div_one]

theorem exists_torus_max {ι : Type} [Fintype ι] (f : MvPolynomial ι ℂ) :
    ∃ θ₀ : ι → ℝ, ∀ θ, ‖MvPolynomial.eval (torusPoint θ) f‖ ≤
      ‖MvPolynomial.eval (torusPoint θ₀) f‖ := by
  obtain ⟨θ₀, -, hθ₀⟩ := (isCompact_univ_pi (fun _ : ι => isCompact_Icc (a := (0 : ℝ)) (b := 1))).exists_isMaxOn
    ⟨fun _ => 0, fun i _ => by simp⟩ (continuous_eval_torus f).norm.continuousOn
  refine ⟨θ₀, fun θ => ?_⟩
  have hmem : (fun i => Int.fract (θ i)) ∈ Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1) :=
    fun i _ => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have h := isMaxOn_iff.mp hθ₀ _ hmem
  simp only [torusPoint_fract] at h
  exact h

theorem torus_l2_cauchy_of_basic (hBasic : TorusMeanBasicStatement) : TorusL2Cauchy := by
  intro ι _ f
  haveI := torusProb_isProb ι
  obtain ⟨hInt, hMul, hMono⟩ := hBasic ι
  constructor
  · intro hf
    set A := ∑ s ∈ f.support, ‖f.coeff s‖ ^ 2 with hA
    have hApos : 0 < A := by
      obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.mp hf)
      exact Finset.sum_pos' (fun _ _ => by positivity)
        ⟨s, hs, pow_pos (norm_pos_iff.mpr (MvPolynomial.mem_support_iff.mp hs)) 2⟩
    have hq : 0 < Real.exp 1 / A := div_pos (Real.exp_pos 1) hApos
    set r : ℝ := Real.sqrt (Real.exp 1 / A) with hrdef
    have hr : 0 < r := Real.sqrt_pos.mpr hq
    have hr2 : r ^ 2 = Real.exp 1 / A := Real.sq_sqrt hq.le
    have hc : ((r : ℂ)) ≠ 0 := by exact_mod_cast hr.ne'
    have hcn : ‖(r : ℂ)‖ = r := by simp [abs_of_pos hr]
    have hCc : (MvPolynomial.C (r : ℂ) : MvPolynomial ι ℂ) ≠ 0 := by simpa using hc
    have hmean : torusMean (MvPolynomial.C (r : ℂ) * f) = Real.log r + torusMean f := by
      rw [hMul _ _ hCc hf, MvPolynomial.C_apply, hMono, hcn]
    have hpt : ∀ θ, Real.log ‖MvPolynomial.eval (torusPoint θ) (MvPolynomial.C (r : ℂ) * f)‖ ≤
        r ^ 2 / Real.exp 1 * ‖MvPolynomial.eval (torusPoint θ) f‖ ^ 2 / 2 := by
      intro θ
      rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, norm_mul, hcn]
      have hx : 0 ≤ ‖MvPolynomial.eval (torusPoint θ) f‖ := norm_nonneg _
      rcases hx.eq_or_lt with h0 | hpos
      · rw [← h0]; simp
      · have hy : 0 < (r * ‖MvPolynomial.eval (torusPoint θ) f‖) ^ 2 / Real.exp 1 := by positivity
        have h1 := Real.log_le_sub_one_of_pos hy
        rw [Real.log_div (ne_of_gt (by positivity)) (Real.exp_pos 1).ne', Real.log_exp,
          Real.log_pow] at h1
        have e2 : (r * ‖MvPolynomial.eval (torusPoint θ) f‖) ^ 2 / Real.exp 1 =
            r ^ 2 / Real.exp 1 * ‖MvPolynomial.eval (torusPoint θ) f‖ ^ 2 := by ring
        push_cast at h1
        linarith
    have hint2 : Integrable (fun θ => ‖MvPolynomial.eval (torusPoint θ) f‖ ^ 2) (torusProb ι) :=
      integrable_of_bdd ((continuous_eval_torus f).norm.pow 2) ((∑ s ∈ f.support, ‖f.coeff s‖) ^ 2)
        (fun θ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_eval_torus_le f θ) 2)
    have hle : torusMean (MvPolynomial.C (r : ℂ) * f) ≤ r ^ 2 / Real.exp 1 * A / 2 := by
      unfold torusMean
      calc _ ≤ ∫ θ, r ^ 2 / Real.exp 1 * ‖MvPolynomial.eval (torusPoint θ) f‖ ^ 2 / 2 ∂(torusProb ι) :=
            integral_mono (hInt _ (mul_ne_zero hCc hf)) ((hint2.const_mul _).div_const 2) hpt
        _ = r ^ 2 / Real.exp 1 * A / 2 := by
            rw [integral_div, integral_const_mul, torus_parseval]
    have h12 : r ^ 2 / Real.exp 1 * A / 2 = 1 / 2 := by
      rw [hr2]; field_simp
    have hlogr : Real.log r = (1 - Real.log A) / 2 := by
      rw [hrdef, Real.log_sqrt hq.le, Real.log_div (Real.exp_pos 1).ne' hApos.ne', Real.log_exp]
    unfold polyL2
    rw [← hA, Real.log_sqrt hApos.le]
    linarith
  · intro s
    obtain ⟨θ₀, hθ₀⟩ := exists_torus_max f
    refine ⟨θ₀, ?_⟩
    rw [← torus_coeff_integral f s]
    have hb : ∀ᵐ θ ∂(torusProb ι), ‖MvPolynomial.eval (torusPoint θ) f * conj (torusMono θ s)‖ ≤
        ‖MvPolynomial.eval (torusPoint θ₀) f‖ :=
      Filter.Eventually.of_forall (fun θ => by simpa [norm_torusMono_eq_one] using hθ₀ θ)
    simpa using norm_integral_le_of_norm_le_const hb

end ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Metric Set Real

theorem gauss_pair {n : ℕ} (hn : 0 < n) (c : EuclideanSpace ℂ (Fin n)) (hc : c ≠ 0) :
    ∃ s : ℝ, 0 < s ∧
      Integrable (fun x : EuclideanSpace ℂ (Fin n) ↦
        log ‖∑ i, WithLp.ofLp c i * WithLp.ofLp x i‖ * exp (-‖x‖ ^ 2)) ∧
      ∫ x : EuclideanSpace ℂ (Fin n), log ‖∑ i, WithLp.ofLp c i * WithLp.ofLp x i‖ *
        exp (-‖x‖ ^ 2) = s * (gaussLogC ‖c‖ * gaussOneC ^ (n - 1)) ∧
      ∫ x : EuclideanSpace ℂ (Fin n), exp (-‖x‖ ^ 2) = s * gaussOneC ^ n := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  set v : EuclideanSpace ℂ (Fin (m + 1)) := WithLp.toLp 2 (fun i => star (WithLp.ofLp c i)) with hvdef
  have hvx : ∀ x : EuclideanSpace ℂ (Fin (m + 1)),
      inner ℂ v x = ∑ i, WithLp.ofLp c i * WithLp.ofLp x i := by
    intro x
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hvdef, RCLike.inner_apply] <;> ring
  have hvn : ‖v‖ = ‖c‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp [hvdef]
  have hc0 : 0 < ‖c‖ := norm_pos_iff.mpr hc
  set u0 : EuclideanSpace ℂ (Fin (m + 1)) := ((‖c‖⁻¹ : ℝ) : ℂ) • v with hu0
  have hu0n : ‖u0‖ = 1 := by
    rw [hu0, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hc0, hvn,
      inv_mul_cancel₀ hc0.ne']
  have hon : Orthonormal ℂ (Set.restrict ({0} : Set (Fin (m + 1))) (fun _ => u0)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j :=
      Subtype.ext (by rw [Set.mem_singleton_iff.mp i.2, Set.mem_singleton_iff.mp j.2])
    subst hij
    simp only [Set.restrict_apply, if_true]
    rw [inner_self_eq_norm_sq_to_K]
    show ((‖u0‖ : ℝ) : ℂ) ^ 2 = 1
    rw [hu0n]; simp
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℂ)
    (by rw [finrank_euclideanSpace]) hon
  have hb0 : b 0 = u0 := hb 0 (Set.mem_singleton 0)
  let M : EuclideanSpace ℂ (Fin (m + 1)) ≃L[ℂ] (Fin (m + 1) → ℂ) :=
    b.repr.toContinuousLinearEquiv.trans (EuclideanSpace.equiv (Fin (m + 1)) ℂ)
  have hMr : ∀ x i, M x i = b.repr x i := fun x i => rfl
  have hnorm1 : ∀ x : EuclideanSpace ℂ (Fin (m + 1)), ‖∑ i, WithLp.ofLp c i * WithLp.ofLp x i‖ = ‖c‖ * ‖M x 0‖ := by
    intro x
    rw [hMr, OrthonormalBasis.repr_apply_apply, hb0, hu0, inner_smul_left, hvx, norm_mul,
      Complex.conj_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hc0,
      ← mul_assoc, mul_inv_cancel₀ hc0.ne', one_mul]
  have hnorm2 : ∀ x : EuclideanSpace ℂ (Fin (m + 1)), ‖x‖ ^ 2 = ∑ i, ‖M x i‖ ^ 2 := by
    intro x
    rw [← b.repr.norm_map x, EuclideanSpace.norm_sq_eq]
    rfl
  let f : Fin (m + 1) → ℂ → ℝ := fun i z =>
    if i = 0 then log (‖c‖ * ‖z‖) * exp (-‖z‖ ^ 2) else exp (-‖z‖ ^ 2)
  let g : Fin (m + 1) → ℂ → ℝ := fun _ z => exp (-‖z‖ ^ 2)
  have hexp : ∀ y : Fin (m + 1) → ℂ, exp (-∑ i, ‖y i‖ ^ 2) = ∏ i, exp (-‖y i‖ ^ 2) := by
    intro y; rw [← Real.exp_sum, Finset.sum_neg_distrib]
  have hf : ∀ y : Fin (m + 1) → ℂ,
      ∏ i, f i (y i) = log (‖c‖ * ‖y 0‖) * ∏ i, exp (-‖y i‖ ^ 2) := by
    intro y
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ (fun i => exp (-‖y i‖ ^ 2))]
    simp only [f, if_pos rfl, Fin.succ_ne_zero, if_false]
    ring
  have hF1 : ∀ x : EuclideanSpace ℂ (Fin (m + 1)),
      log ‖∑ i, WithLp.ofLp c i * WithLp.ofLp x i‖ * exp (-‖x‖ ^ 2) = ∏ i, f i (M x i) := by
    intro x
    rw [hf (M x), hnorm1, hnorm2, hexp]
  have hF2 : ∀ x : EuclideanSpace ℂ (Fin (m + 1)), exp (-‖x‖ ^ 2) = ∏ i, g i (M x i) := by
    intro x
    rw [hnorm2, hexp]
  set μ := (volume : Measure (EuclideanSpace ℂ (Fin (m + 1)))) with hμ
  let Me := M.toHomeomorph.toMeasurableEquiv
  haveI : (μ.map Me).IsAddHaarMeasure := by
    have h := M.isAddHaarMeasure_map μ
    exact h
  set k := (μ.map Me).addHaarScalarFactor (volume : Measure (Fin (m + 1) → ℂ))
  have hν : μ.map Me = k • (volume : Measure (Fin (m + 1) → ℂ)) :=
    Measure.isAddLeftInvariant_eq_smul _ _
  have hk : 0 < k := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hint : ∀ H : (Fin (m + 1) → ℂ) → ℝ, ∫ x, H (M x) ∂μ = (k : ℝ) * ∫ y, H y := by
    intro H
    calc ∫ x, H (M x) ∂μ = ∫ x, H (Me x) ∂μ := rfl
      _ = ∫ y, H y ∂(μ.map Me) := (Me.measurableEmbedding.integral_map H).symm
      _ = (k : ℝ) * ∫ y, H y := by
        rw [hν, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
  have hintg : ∀ H : (Fin (m + 1) → ℂ) → ℝ, Integrable H → Integrable (fun x => H (M x)) μ := by
    intro H hH
    have h1 : Integrable H (μ.map Me) := by rw [hν]; exact hH.smul_measure_nnreal
    exact Me.measurableEmbedding.integrable_map_iff.mp h1
  have hP1 : ∫ y : Fin (m + 1) → ℂ, ∏ i, f i (y i) = gaussLogC ‖c‖ * gaussOneC ^ m := by
    rw [volume_pi, integral_fintype_prod_eq_prod (f := f), Fin.prod_univ_succ]
    simp only [f, if_pos rfl, Fin.succ_ne_zero, if_false, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, gaussLogC, gaussOneC]
  have hP2 : ∫ y : Fin (m + 1) → ℂ, ∏ i, g i (y i) = gaussOneC ^ (m + 1) := by
    rw [volume_pi, integral_fintype_prod_eq_prod (f := g)]
    simp only [g, Finset.prod_const, Finset.card_univ, Fintype.card_fin, gaussOneC]
  have hI1 : Integrable (fun y : Fin (m + 1) → ℂ => ∏ i, f i (y i)) := by
    rw [volume_pi]
    refine Integrable.fintype_prod (f := f) fun i => ?_
    by_cases hi : i = 0
    · subst hi; simpa [f] using integrable_gaussLogC hc0
    · simpa [f, hi] using integrable_gaussOneC
  refine ⟨(k : ℝ), NNReal.coe_pos.mpr hk, ?_, ?_, ?_⟩
  · exact (hintg _ hI1).congr (Filter.Eventually.of_forall fun x => (hF1 x).symm)
  · rw [show (fun x : EuclideanSpace ℂ (Fin (m + 1)) =>
        log ‖∑ i, WithLp.ofLp c i * WithLp.ofLp x i‖ * exp (-‖x‖ ^ 2)) =
        fun x => ∏ i, f i (M x i) from funext hF1]
    rw [hint (fun y => ∏ i, f i (y i)), hP1]
  · rw [show (fun x : EuclideanSpace ℂ (Fin (m + 1)) => exp (-‖x‖ ^ 2)) =
        fun x => ∏ i, g i (M x i) from funext hF2]
    rw [hint (fun y => ∏ i, g i (y i)), hP2]

end ReciprocityTheory.MultiplicativeHeights
end
end
