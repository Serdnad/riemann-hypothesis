module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.LinearAlgebra.Matrix.DotProduct

@[expose] public section

section

open Matrix Finset Real

namespace GlobalTheory

private theorem log_le_sqrt_of_one_le (x : ℝ) (hx : 1 ≤ x) :
    Real.log x ≤ Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hx2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
  have h1 : Real.log (Real.sqrt x / 2) ≤ Real.sqrt x / 2 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Real.log (Real.sqrt x / 2) = Real.log (Real.sqrt x) - Real.log 2 :=
    Real.log_div hs.ne' (by norm_num)
  have h3 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    conv_lhs => rw [← hx2]
    rw [Real.log_pow]
    push_cast
    ring
  have h4 := Real.log_two_lt_d9
  linarith



theorem gap_threshold_pays_far_terms : ∀ (Cg : ℝ) (n f q : ℕ) (rd g b : ℝ) (h t : ℝ), 0 ≤ Cg → 3 ≤ n → 1 ≤ f → 1 ≤ q → q ^ 2 ≤ n → 1 ≤ rd → Real.log f ≤ Real.sqrt n → 2 ≤ b → 1 ≤ g → g ≤ b ^ Cg → 8 * 10 ^ 14 * (Cg + 4) * (n : ℝ) ^ 19 * (f : ℝ) ^ 5 * Real.log (b * rd) ≤ h → ((n : ℝ) * f * rd * g * b)⁻¹ ^ (11 * q) ≤ t → t ≤ 1 / 2 → let ep : ℝ := 1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2); 64 * (n : ℝ) ^ 2 ≤ h * ep ∧ 1 ≤ h * ep ^ 2 / 16 ∧ (3 * Real.sqrt n / t ^ 2) ^ (2 * (n ^ 2 * f)) * (2 * f * 3 ^ f * Real.exp (-(h * ep ^ 2 / 16))) ≤ Real.exp (-((n : ℝ) ^ 2 * f)) := by
  intro Cg n f q rd g b h t hCg hn hf hq hqn hrd hlogf hb hg1 hgb hh ht1 _ht2 ep
  have hep : ep = 1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2) := rfl
  clear_value ep
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hqnR : (q : ℝ) ^ 2 ≤ n := by exact_mod_cast hqn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hf0 : (f : ℝ) ≠ 0 := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hfpos : (0 : ℝ) < f := by linarith
  set s := Real.sqrt (n : ℝ) with hs_def
  have hs2 : s ^ 2 = n := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ s := Real.one_le_sqrt.2 (by linarith)
  have hsn : s ≤ n := by nlinarith
  have hqs : (q : ℝ) ≤ s := (Real.le_sqrt (by positivity) (by linarith)).2 hqnR
  set ℓ := Real.log (b * rd) with hℓ_def
  have hbrd : 2 ≤ b * rd := le_trans hb (le_mul_of_one_le_right (by linarith) hrd)
  have hℓ : 0.69 ≤ ℓ := by
    have e1 := Real.log_le_log (by norm_num) hbrd
    have e2 := Real.log_two_gt_d9
    linarith
  have hlogb : Real.log b ≤ ℓ := Real.log_le_log (by linarith) (le_mul_of_one_le_right (by linarith) hrd)
  have hlogb0 : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
  have hKl : 2.76 ≤ (Cg + 4) * ℓ := by nlinarith [mul_nonneg hCg (by linarith : (0 : ℝ) ≤ ℓ)]

  have hX : 50 * (Cg + 4) * (n : ℝ) ^ 3 * f * ℓ ≤ h * ep ^ 2 / 16 := by
    have e : 8 * 10 ^ 14 * (Cg + 4) * (n : ℝ) ^ 19 * (f : ℝ) ^ 5 * ℓ * ep ^ 2 / 16
        = 50 * (Cg + 4) * (n : ℝ) ^ 3 * f * ℓ := by
      rw [hep]
      field_simp
      norm_num
    rw [← e]
    have := mul_le_mul_of_nonneg_right hh (sq_nonneg ep)
    linarith
  have hn3f : 1 ≤ (n : ℝ) ^ 3 * f := by
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) hfR
  refine ⟨?_, ?_, ?_⟩
  · have e : 8 * 10 ^ 14 * (Cg + 4) * (n : ℝ) ^ 19 * (f : ℝ) ^ 5 * ℓ * ep
        = 800000000 * ((Cg + 4) * ℓ) * ((n : ℝ) ^ 11 * f ^ 3) := by
      rw [hep]
      field_simp
      norm_num
    have hep0 : 0 ≤ ep := by rw [hep]; positivity
    have h1 := mul_le_mul_of_nonneg_right hh hep0
    have hn11 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 11 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have hf3 : (1 : ℝ) ≤ (f : ℝ) ^ 3 := one_le_pow₀ hfR
    have hP : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 11 * f ^ 3 :=
      le_trans hn11 (le_mul_of_one_le_right (by positivity) hf3)
    have h2 : 2.76 * (n : ℝ) ^ 2 ≤ ((Cg + 4) * ℓ) * ((n : ℝ) ^ 11 * f ^ 3) :=
      mul_le_mul hKl hP (by positivity) (by linarith)
    have hz : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
    linarith
  · have h2 : 2.76 * 1 ≤ ((Cg + 4) * ℓ) * ((n : ℝ) ^ 3 * f) :=
      mul_le_mul hKl hn3f (by norm_num) (by linarith)
    linarith
  · set X := h * ep ^ 2 / 16 with hX_def
    set M := (n : ℝ) * f * rd * g * b with hM_def
    have hgpos : 0 < g := by linarith
    have hMpos : 0 < M := by
      have : (0 : ℝ) < rd := by linarith
      have : (0 : ℝ) < b := by linarith
      positivity
    set Lb := s + s + Cg * ℓ + ℓ with hLb_def
    have hLb0 : 0 ≤ Lb := by
      have : 0 ≤ Cg * ℓ := mul_nonneg hCg (by linarith)
      linarith

    have hnexp : (n : ℝ) ≤ Real.exp s := by
      calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hnpos).symm
        _ ≤ Real.exp s := Real.exp_le_exp.2 (log_le_sqrt_of_one_le _ (by linarith))
    have hfexp : (f : ℝ) ≤ Real.exp s := by
      calc (f : ℝ) = Real.exp (Real.log f) := (Real.exp_log hfpos).symm
        _ ≤ Real.exp s := Real.exp_le_exp.2 hlogf
    have hgexp : g ≤ Real.exp (Cg * ℓ) := by
      calc g ≤ b ^ Cg := hgb
        _ = Real.exp (Real.log b * Cg) := Real.rpow_def_of_pos (by linarith) Cg
        _ ≤ Real.exp (Cg * ℓ) := by
          apply Real.exp_le_exp.2
          have := mul_le_mul_of_nonneg_right hlogb hCg
          linarith
    have hbrdexp : b * rd = Real.exp ℓ := (Real.exp_log (by linarith)).symm
    have hMle : M ≤ Real.exp Lb := by
      have e1 : M = (n : ℝ) * f * g * (b * rd) := by rw [hM_def]; ring
      have e2 : Real.exp Lb = Real.exp s * Real.exp s * Real.exp (Cg * ℓ) * Real.exp ℓ := by
        rw [hLb_def, Real.exp_add, Real.exp_add, Real.exp_add]
      rw [e1, e2, hbrdexp]
      have a1 : (n : ℝ) * f ≤ Real.exp s * Real.exp s :=
        mul_le_mul hnexp hfexp (by positivity) (by positivity)
      have a2 : (n : ℝ) * f * g ≤ Real.exp s * Real.exp s * Real.exp (Cg * ℓ) :=
        mul_le_mul a1 hgexp (by linarith) (by positivity)
      exact mul_le_mul_of_nonneg_right a2 (by positivity)

    have htpos : 0 < t := lt_of_lt_of_le (pow_pos (inv_pos.2 hMpos) _) ht1
    have hinvt : t⁻¹ ≤ Real.exp (11 * s * Lb) := by
      rw [inv_pow] at ht1
      have a1 : t⁻¹ ≤ M ^ (11 * q) := inv_le_of_inv_le₀ (pow_pos hMpos _) ht1
      have a2 : M ^ (11 * q) ≤ Real.exp Lb ^ (11 * q) := pow_le_pow_left₀ hMpos.le hMle _
      have a3 : Real.exp Lb ^ (11 * q) = Real.exp (((11 * q : ℕ) : ℝ) * Lb) := by
        rw [Real.exp_nat_mul]
      have a4 : ((11 * q : ℕ) : ℝ) * Lb ≤ 11 * s * Lb := by
        push_cast
        have : 11 * (q : ℝ) ≤ 11 * s := by linarith
        exact mul_le_mul_of_nonneg_right this hLb0
      calc t⁻¹ ≤ M ^ (11 * q) := a1
        _ ≤ Real.exp Lb ^ (11 * q) := a2
        _ = Real.exp (((11 * q : ℕ) : ℝ) * Lb) := a3
        _ ≤ Real.exp (11 * s * Lb) := Real.exp_le_exp.2 a4

    have hA : 3 * s / t ^ 2 ≤ Real.exp (2 + s + 22 * s * Lb) := by
      have e1 : 3 * s / t ^ 2 = 3 * s * (t⁻¹) ^ 2 := by rw [div_eq_mul_inv, inv_pow]
      have e2 : Real.exp (2 + s + 22 * s * Lb)
          = Real.exp 2 * Real.exp s * (Real.exp (11 * s * Lb)) ^ 2 := by
        rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [e1, e2]
      have b1 : (3 : ℝ) ≤ Real.exp 2 := by
        have := Real.add_one_le_exp 2
        linarith
      have b2 : s ≤ Real.exp s := by
        have := Real.add_one_le_exp s
        linarith
      have b3 : (t⁻¹) ^ 2 ≤ (Real.exp (11 * s * Lb)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hinvt 2
      have b4 : 3 * s ≤ Real.exp 2 * Real.exp s :=
        mul_le_mul b1 b2 (by linarith) (by positivity)
      exact mul_le_mul b4 b3 (by positivity) (by positivity)
    have hpow : (3 * s / t ^ 2) ^ (2 * (n ^ 2 * f))
        ≤ Real.exp (((2 * (n ^ 2 * f) : ℕ) : ℝ) * (2 + s + 22 * s * Lb)) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by positivity) hA _

    have hsmall : 2 * (f : ℝ) * 3 ^ f ≤ Real.exp (4 * f) := by
      have c1 : 2 * (f : ℝ) ≤ Real.exp (2 * f) := by
        have := Real.add_one_le_exp (2 * (f : ℝ))
        linarith
      have c2 : (3 : ℝ) ^ f ≤ Real.exp (f * 2) := by
        rw [Real.exp_nat_mul]
        have : (3 : ℝ) ≤ Real.exp 2 := by
          have := Real.add_one_le_exp 2
          linarith
        exact pow_le_pow_left₀ (by norm_num) this f
      have e : Real.exp (4 * f) = Real.exp (2 * f) * Real.exp (f * 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [e]
      exact mul_le_mul c1 c2 (by positivity) (by positivity)

    have hexp : ((2 * (n ^ 2 * f) : ℕ) : ℝ) * (2 + s + 22 * s * Lb) + (4 * f + -X)
        ≤ -((n : ℝ) ^ 2 * f) := by
      push_cast
      have hP0 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * f := by positivity
      have hKl0 : 0 ≤ (Cg + 1) * ℓ := mul_nonneg (by linarith) (by linarith)
      have k1 : (n : ℝ) ^ 2 * f * s * ((Cg + 1) * ℓ) ≤ (n : ℝ) ^ 2 * f * n * ((Cg + 1) * ℓ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsn hP0) hKl0
      have k2 : (n : ℝ) ^ 2 * f * s ≤ (n : ℝ) ^ 2 * f * n := mul_le_mul_of_nonneg_left hsn hP0
      have k3 : (f : ℝ) ≤ (n : ℝ) ^ 2 * f :=
        le_mul_of_one_le_left hfpos.le (one_le_pow₀ (by linarith))
      have k4 : (n : ℝ) ^ 2 * f * 3 ≤ (n : ℝ) ^ 2 * f * n := mul_le_mul_of_nonneg_left hnR hP0
      have k5 : (n : ℝ) ^ 2 * f * n * 107 ≤ (n : ℝ) ^ 2 * f * n * (156 * ℓ) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have k6 : 0 ≤ (n : ℝ) ^ 2 * f * n * (Cg * ℓ) :=
        mul_nonneg (by positivity) (mul_nonneg hCg (by linarith))
      have k7 : (n : ℝ) ^ 2 * f * s ^ 2 = (n : ℝ) ^ 2 * f * n := by rw [hs2]
      have k8 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * f * n := by positivity
      rw [hLb_def]
      linarith
    calc (3 * s / t ^ 2) ^ (2 * (n ^ 2 * f)) * (2 * f * 3 ^ f * Real.exp (-X))
        ≤ Real.exp (((2 * (n ^ 2 * f) : ℕ) : ℝ) * (2 + s + 22 * s * Lb))
            * (Real.exp (4 * f) * Real.exp (-X)) := by
          apply mul_le_mul hpow (mul_le_mul_of_nonneg_right hsmall (by positivity))
            (by positivity) (by positivity)
      _ = Real.exp (((2 * (n ^ 2 * f) : ℕ) : ℝ) * (2 + s + 22 * s * Lb) + (4 * f + -X)) := by
          rw [Real.exp_add, Real.exp_add]
      _ ≤ Real.exp (-((n : ℝ) ^ 2 * f)) := Real.exp_le_exp.2 hexp

end GlobalTheory
end

section

open Matrix Finset Real

namespace GlobalTheory


open MeasureTheory Metric in
theorem card_le_of_separated_in_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (T : Finset E) (R la : ℝ) (hR : 0 ≤ R) (hla : 0 < la)
    (hT : ∀ x ∈ T, ‖x‖ ≤ R) (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → la ≤ ‖x - y‖) :
    (T.card : ℝ) ≤ (1 + 2 * R / la) ^ Module.finrank ℝ E := by
  classical
  rcases subsingleton_or_nontrivial E with hE | hE
  · have h1 : T.card ≤ 1 := Finset.card_le_one_of_subsingleton T
    rw [Module.finrank_zero_of_subsingleton, pow_zero]
    exact_mod_cast h1
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure E, μ.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  have hr : 0 < la / 2 := by positivity
  have hdisj : (T : Set E).PairwiseDisjoint (fun x => ball x (la / 2)) := by
    intro x hx y hy hxy
    refine Set.disjoint_left.mpr ?_
    intro z hzx hzy
    rw [mem_ball, dist_eq_norm] at hzx hzy
    have h1 := hsep x hx y hy hxy
    have h2 : ‖x - y‖ < la := by
      calc ‖x - y‖ = ‖(z - y) - (z - x)‖ := by congr 1; abel
        _ ≤ ‖z - y‖ + ‖z - x‖ := norm_sub_le _ _
        _ < la / 2 + la / 2 := add_lt_add hzy hzx
        _ = la := by ring
    linarith
  have hsub : (⋃ x ∈ T, ball x (la / 2)) ⊆ ball (0 : E) (R + la / 2) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨x, hx, hzx⟩ := hz
    rw [mem_ball, dist_eq_norm] at hzx ⊢
    calc ‖z - 0‖ = ‖(z - x) + x‖ := by simp
      _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
      _ < la / 2 + R := by linarith [hT x hx]
      _ = R + la / 2 := by ring
  have hle := measure_mono (μ := μ) hsub
  rw [measure_biUnion_finset hdisj (fun x _ => measurableSet_ball)] at hle
  simp only [Measure.addHaar_ball_center, Finset.sum_const, nsmul_eq_mul] at hle
  rw [Measure.addHaar_ball μ 0 hr.le, Measure.addHaar_ball μ 0 (by positivity : (0 : ℝ) ≤ R + la / 2),
    ← mul_assoc] at hle
  have hm0 : μ (ball (0 : E) 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hmtop : μ (ball (0 : E) 1) ≠ ⊤ := measure_ball_lt_top.ne
  rw [ENNReal.mul_le_mul_iff_left hm0 hmtop, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  have hpos : 0 < (la / 2) ^ Module.finrank ℝ E := by positivity
  have hq : (1 + 2 * R / la) ^ Module.finrank ℝ E
      = (R + la / 2) ^ Module.finrank ℝ E / (la / 2) ^ Module.finrank ℝ E := by
    rw [← div_pow]
    congr 1
    field_simp
    ring
  rw [hq, le_div_iff₀ hpos]
  exact hle

theorem packing_geometric_mean_separated : ∀ (ι : Type) [Fintype ι] [Nonempty ι] (W : ι → Type) [∀ v, NormedAddCommGroup (W v)] [∀ v, NormedSpace ℝ (W v)] [∀ v, FiniteDimensional ℝ (W v)] (N : ℕ), 1 ≤ N → (∀ v, Module.finrank ℝ (W v) = N) → ∀ (la : ℝ) (S : Set (∀ v, W v)) (X : ι → ℝ), 0 < la → (∀ v, 0 < X v) → (∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → la ≤ (∏ v, ‖s v - s' v‖) ^ ((1 : ℝ) / Fintype.card ι)) → {s ∈ S | ∀ v, ‖s v‖ ≤ X v}.Finite ∧ (({s ∈ S | ∀ v, ‖s v‖ ≤ X v}.ncard : ℕ) : ℝ) ≤ (1 + 2 * (∏ v, X v) ^ ((1 : ℝ) / Fintype.card ι) / la) ^ (N * Fintype.card ι) := by
  intro ι _ _ W _ _ _ N hN hdim la S X hla hX hsep
  classical
  set k := Fintype.card ι with hk
  have hkpos : 0 < k := Fintype.card_pos
  set P := ∏ v, X v with hP
  have hPpos : 0 < P := Finset.prod_pos (fun v _ => hX v)
  set G := P ^ ((1 : ℝ) / k) with hG
  have hGpos : 0 < G := Real.rpow_pos_of_pos hPpos _
  have hGk : G ^ k = P := by
    rw [hG, one_div]
    exact Real.rpow_inv_natCast_pow hPpos.le hkpos.ne'
  set c : ι → ℝ := fun v => G / X v with hc
  have hcpos : ∀ v, 0 < c v := fun v => div_pos hGpos (hX v)
  have hcprod : ∏ v, c v = 1 := by
    rw [hc, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, ← hk, hGk]
    exact div_self hPpos.ne'
  let φ : (∀ v, W v) → (∀ v, W v) := fun s v => c v • s v
  have hφinj : Function.Injective φ := by
    intro s s' h
    funext v
    exact smul_right_injective _ (hcpos v).ne' (congrFun h v)
  set A := {s ∈ S | ∀ v, ‖s v‖ ≤ X v} with hA
  have hdimPi : Module.finrank ℝ (∀ v, W v) = N * k := by
    rw [Module.finrank_pi_fintype]
    simp [hdim, hk, mul_comm]
  have key : ∀ F : Finset (∀ v, W v), (↑F : Set (∀ v, W v)) ⊆ A →
      (F.card : ℝ) ≤ (1 + 2 * G / la) ^ (N * k) := by
    intro F hF
    have hbound := card_le_of_separated_in_ball (F.image φ) G la hGpos.le hla ?_ ?_
    · rw [Finset.card_image_of_injective _ hφinj, hdimPi] at hbound
      exact hbound
    · intro y hy
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
      have hsA := hF hs
      refine (pi_norm_le_iff_of_nonneg hGpos.le).mpr (fun v => ?_)
      simp only [φ, norm_smul, Real.norm_eq_abs, abs_of_pos (hcpos v)]
      calc c v * ‖s v‖ ≤ c v * X v := mul_le_mul_of_nonneg_left (hsA.2 v) (hcpos v).le
        _ = G := by
          simp only [hc]
          field_simp [(hX v).ne']
    · intro y hy y' hy' hne
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hy'
      have hss : s ≠ s' := fun h => hne (by rw [h])
      have h1 := hsep s (hF hs).1 s' (hF hs').1 hss
      have hprod : ∏ v, ‖(φ s - φ s') v‖ = ∏ v, ‖s v - s' v‖ := by
        simp only [φ, Pi.sub_apply, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (hcpos _),
          Finset.prod_mul_distrib, hcprod, one_mul]
      have hgm : (∏ v, ‖(φ s - φ s') v‖) ^ ((1 : ℝ) / k) ≤ ‖φ s - φ s'‖ := by
        have hle : ∏ v, ‖(φ s - φ s') v‖ ≤ ‖φ s - φ s'‖ ^ k := by
          rw [hk, ← Finset.card_univ, ← Finset.prod_const]
          exact Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) (fun v _ => norm_le_pi_norm _ v)
        calc (∏ v, ‖(φ s - φ s') v‖) ^ ((1 : ℝ) / k) ≤ (‖φ s - φ s'‖ ^ k) ^ ((1 : ℝ) / k) :=
              Real.rpow_le_rpow (Finset.prod_nonneg (fun v _ => norm_nonneg _)) hle (by positivity)
          _ = ‖φ s - φ s'‖ := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
                mul_one_div_cancel (by exact_mod_cast hkpos.ne'), Real.rpow_one]
      rw [hprod] at hgm
      exact h1.trans hgm
  have hfin : A.Finite := by
    by_contra hinf
    obtain ⟨F, hF, hcard⟩ :=
      Set.Infinite.exists_subset_card_eq hinf (⌈(1 + 2 * G / la) ^ (N * k)⌉₊ + 1)
    have h3 := key F hF
    rw [hcard] at h3
    push_cast at h3
    linarith [Nat.le_ceil ((1 + 2 * G / la) ^ (N * k))]
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card A hfin]
  exact key _ (by simp)

end GlobalTheory
end

section

open Matrix Finset Real

namespace GlobalTheory


open scoped ComplexOrder in
theorem unipotent_isometry_definite_eq_one :
    ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ), c ≠ 0 → Aᴴ * (c • (1 : Matrix (Fin n) (Fin n) ℂ)) * A = c • 1 → (A - 1) ^ m = 0 → A = 1 := by
  intro n m A c hc hA hm

  have hU : Aᴴ * A = 1 := by
    have h1 : c • (Aᴴ * A) = c • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [← hA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    exact smul_right_injective _ hc h1
  have hU' : A * Aᴴ = 1 := mul_eq_one_comm.mp hU

  have hcomm : Commute (A - 1)ᴴ (A - 1) := by
    show (A - 1)ᴴ * (A - 1) = (A - 1) * (A - 1)ᴴ
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, sub_mul, mul_sub, hU, hU',
      one_mul, mul_one]
    abel
  have hN : (A - 1) ^ (m + 1) = 0 := by rw [pow_succ, hm, zero_mul]

  have hBh : ((A - 1)ᴴ * (A - 1))ᴴ = (A - 1)ᴴ * (A - 1) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hB : ((A - 1)ᴴ * (A - 1)) ^ (m + 1) = 0 := by
    rw [hcomm.mul_pow, hN, mul_zero]
  have key : ∀ k : ℕ, ((A - 1)ᴴ * (A - 1)) ^ (k + 1) = 0 → (A - 1)ᴴ * (A - 1) = 0 := by
    intro k
    induction k with
    | zero => intro h; simpa using h
    | succ k ih =>
      intro hk
      apply ih
      have h2 : (((A - 1)ᴴ * (A - 1)) ^ (k + 1))ᴴ * ((A - 1)ᴴ * (A - 1)) ^ (k + 1) = 0 := by
        rw [Matrix.conjTranspose_pow, hBh, ← pow_add,
          show k + 1 + (k + 1) = (k + 1 + 1) + k by omega, pow_add, hk, zero_mul]
      exact Matrix.conjTranspose_mul_self_eq_zero.mp h2
  exact sub_eq_zero.mp (Matrix.conjTranspose_mul_self_eq_zero.mp (key m hB))

end GlobalTheory
end

section

namespace GlobalTheory.SublatticeFacts

open Matrix

theorem finiteRing_sq_sub_mul_sq_eq_of_card {A : Type} [CommRing A] {S : Subring A} {n : Type} [Fintype n] [DecidableEq n]
    (Λ : Submodule (↥S) (n → A)) (hfg : Submodule.FG Λ)
    (hden : ∀ (v : n → A), ∃ (N : ℕ), (1 : ℕ) ≤ N ∧ (↑N : A) • v ∈ Λ) (X : Matrix n n A) :
    ∃ (N : ℕ), (1 : ℕ) ≤ N ∧ ∀ y ∈ Λ, (↑N : A) • Matrix.mulVec X y ∈ Λ := by
  classical
  obtain ⟨t, rfl⟩ := hfg
  choose f hf1 hf using fun v : n → A => hden (X *ᵥ v)
  refine ⟨∏ v ∈ t, f v, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun v _ => by have := hf1 v; omega)
  · intro y hy
    rw [Nat.cast_smul_eq_nsmul A]
    induction hy using Submodule.span_induction with
    | mem x hx =>
      rw [← Finset.mul_prod_erase t f hx, mul_nsmul, ← Nat.cast_smul_eq_nsmul A (f x)]
      exact Submodule.smul_of_tower_mem _ (∏ v ∈ t.erase x, f v) (hf x)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [Matrix.mulVec_add, smul_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have : X *ᵥ (a • x) = a • (X *ᵥ x) := by
        ext i
        simp [Matrix.mulVec, dotProduct, Finset.mul_sum, Subring.smul_def, mul_left_comm]
      rw [this, smul_comm]
      exact Submodule.smul_mem _ a hx

theorem main : ∀ {A : Type} [inst : CommRing A] {S : Subring A} {n : Type} [inst_1 : Fintype n] [DecidableEq n]
    (Λ : Submodule (↥S) (n → A)), Submodule.FG Λ →
    (∀ (v : n → A), ∃ (N : ℕ), (1 : ℕ) ≤ N ∧ (↑N : A) • v ∈ Λ) →
    ∀ (X : Matrix n n A), ∃ (N : ℕ), (1 : ℕ) ≤ N ∧ ∀ y ∈ Λ, (↑N : A) • Matrix.mulVec X y ∈ Λ :=
  fun Λ hfg hden X => finiteRing_sq_sub_mul_sq_eq_of_card Λ hfg hden X

end GlobalTheory.SublatticeFacts
end
