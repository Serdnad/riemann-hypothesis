module

public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightPtsIntegralPoints
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle023
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle010
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle016
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def CurvePointsFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι)),
    IsArithVar W 1 → Finite (GroundTheory.Heights₂.Heights.projPts W)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem blockWeight_cast_eq_unitDeg {K : Type} [DecidableEq K] (ι : K → Type) (b : K) (i : ι b) :
    (fun k => ((blockWeight ι ⟨b, i⟩ k : ℕ) : ℤ)) = unitDeg b := by
  funext k
  simp only [blockWeight, unitDeg, Pi.single_apply]
  split_ifs <;> rfl


open Classical in
theorem IntersectionRecursion.proof : IntersectionRecursion.Statement.{u} := by
  intro F _ K _ _ ι _ q d hq hdim b i hX bs
  have : q.IsPrime := hq.isPrime
  set x : MRing ι F := X ⟨b, i⟩ with hxdef
  set J : Ideal (MRing ι F) := q ⊔ Ideal.span {x} with hJdef
  have hx : IsMultiHomog x (blockWeight ι ⟨b, i⟩) := isWeightedHomogeneous_X F _ _

  have hlt : ringKrullDim (MRing ι F ⧸ q) < ((d + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [hdim]
    exact_mod_cast (by omega : d + 1 + Fintype.card K < d + 2 + Fintype.card K)
  have hcut := CutByForm.full F K ι d q hq.isPrime hq.multiHomog hlt x (blockWeight ι ⟨b, i⟩) hx hX bs
  rw [blockWeight_cast_eq_unitDeg] at hcut
  rw [hcut, cycEval]

  have hle : q ≤ J := le_sup_left
  have hr : Ideal.Quotient.mk q x ∈ nonZeroDivisors (MRing ι F ⧸ q) :=
    mem_nonZeroDivisors_of_ne_zero fun h => hX (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hsucc : ringKrullDim (MRing ι F ⧸ J) + 1 ≤ ringKrullDim (MRing ι F ⧸ q) :=
    ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle)
      (Ideal.Quotient.factor_surjective hle) hr (by
        rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_sup_right (Ideal.subset_span rfl))
  rw [hdim] at hsucc
  have hJlt : ringKrullDim (MRing ι F ⧸ J) < ((d + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) := by
    have h := HilbDegBound.lt_of_add_one_le_natCast hsucc
    rwa [show d + 1 + Fintype.card K = d + Fintype.card K + 1 by omega] at h
  have hJh : IsMultiHomogIdeal J := isMultiHomogIdeal_sup_span_of_form hq.multiHomog hx

  refine finsum_congr fun W => ?_
  unfold divCycle
  by_cases hW : W ∈ J.minimalPrimes ∧ IsRelevant W
  · rw [dite_eq_left hW]
    have hWp : W.IsPrime := hW.1.1.1
    have hWh : IsMultiHomogIdeal W := MinimalPrimeMultiHomog.proof F K ι J W hJh hW.1
    have hWle : ringKrullDim (MRing ι F ⧸ W) ≤ ringKrullDim (MRing ι F ⧸ J) :=
      ringKrullDim_le_of_surjective (Ideal.Quotient.factor hW.1.1.2)
        (Ideal.Quotient.factor_surjective hW.1.1.2)
    by_cases hWd : ringKrullDim (MRing ι F ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)
    · rw [dite_eq_left ⟨⟨hWp, hWh, hW.2⟩, hW.1.1.2, hWd⟩]
    · rw [dite_eq_right fun h => hWd h.2.2]
      have hWlt : ringKrullDim (MRing ι F ⧸ W) < ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
        exact lt_of_le_of_ne
          (HilbDegBound.le_natCast_of_lt_natCast_succ (lt_of_le_of_lt hWle hJlt)) hWd
      rw [IntNumVanish.full F K ι d W hWp hWh (Or.inr hWlt) bs, mul_zero]
  · rw [dite_eq_right hW, zero_mul, dite_eq_right]
    rintro ⟨hWq, hJW, hWd⟩
    have : W.IsPrime := hWq.isPrime
    refine hW ⟨TopDimMinimal.full _ J W (d + Fintype.card K) hJW hJlt ?_, hWq.relevant⟩
    rw [hWd]
    exact lt_irrefl _

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem MultigradedHilbertPolynomial.proof (h : EventualPolynomial.Statement) :
    MultigradedHilbertPolynomial.Statement.{u} := by
  intro F _ K _ _ ι _ q d hq hdim
  have hlt : ringKrullDim (MRing ι F ⧸ q) < (((d + 1) + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [hdim]
    exact_mod_cast (by omega : d + Fintype.card K < d + 1 + Fintype.card K)
  have hdeg : DegLT (hilbFn q) (d + 1) :=
    HilbDegBound.full F K ι (d + 1) q hq.isPrime hq.multiHomog hlt
  exact h K d (hilbFn q) hdeg

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Finset Filter Asymptotics

theorem GridSum.choose_antidiagonal (m i j : ℕ) :
    ∑ p ∈ antidiagonal m, p.1.choose i * p.2.choose j = (m + 1).choose (i + j + 1) := by
  induction m generalizing i with
  | zero =>
    cases i <;> cases j <;> simp <;> exact (Nat.choose_eq_zero_of_lt (by omega)).symm
  | succ m ih =>
    rw [Finset.Nat.sum_antidiagonal_succ]
    cases i with
    | zero =>
      have h := ih 0
      simp only [Nat.choose_zero_right, one_mul, zero_add] at h ⊢
      rw [h, Nat.choose_succ_succ (m + 1) j]
    | succ i =>
      have h1 := ih i
      have h2 := ih (i + 1)
      have e : ∀ p : ℕ × ℕ, (p.1 + 1).choose (i + 1) * p.2.choose j =
          p.1.choose i * p.2.choose j + p.1.choose (i + 1) * p.2.choose j := fun p ↦ by
        rw [Nat.choose_succ_succ', add_mul]
      simp only [Nat.choose_zero_succ, zero_mul, zero_add, e, Finset.sum_add_distrib, h1, h2]
      rw [show i + 1 + j + 1 = (i + j + 1) + 1 by omega, Nat.choose_succ_succ' (m + 1) (i + j + 1)]

theorem GridSum.choose_range (n i j : ℕ) :
    ∑ a ∈ range n, a.choose i * (n - 1 - a).choose j = n.choose (i + j + 1) := by
  cases n with
  | zero => simp
  | succ m =>
    rw [← GridSum.choose_antidiagonal m i j, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp

theorem GridSum.choose_le_pow_div_factorial (a i : ℕ) :
    (a.choose i : ℝ) ≤ (a : ℝ) ^ i / (i.factorial : ℝ) := by
  rw [le_div_iff₀ (by positivity)]
  have h : a.choose i * i.factorial ≤ a ^ i := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow a i
  exact_mod_cast h

theorem GridSum.pow_div_factorial_le (a i : ℕ) :
    (a : ℝ) ^ i / (i.factorial : ℝ) ≤ ((a + i).choose i : ℝ) := by
  rw [div_le_iff₀ (by positivity)]
  have h : a ^ i ≤ (a + i).choose i * i.factorial := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
    calc a ^ i ≤ (a + i + 1 - i) ^ i := Nat.pow_le_pow_left (by omega) i
      _ ≤ (a + i).descFactorial i := Nat.pow_sub_le_descFactorial _ _
  exact_mod_cast h

theorem GridSum.pow_sub_pow_le (x y : ℝ) (k : ℕ) (hy : 0 ≤ y) (hxy : y ≤ x) :
    x ^ k - y ^ k ≤ k * (x - y) * x ^ (k - 1) := by
  rw [← geom_sum₂_mul]
  have hx : 0 ≤ x := hy.trans hxy
  have hs : ∑ l ∈ range k, x ^ l * y ^ (k - 1 - l) ≤ k * x ^ (k - 1) := by
    calc ∑ l ∈ range k, x ^ l * y ^ (k - 1 - l) ≤ ∑ l ∈ range k, x ^ (k - 1) := by
          apply sum_le_sum
          intro l hl
          have hl' : l + (k - 1 - l) = k - 1 := by have := mem_range.mp hl; omega
          calc x ^ l * y ^ (k - 1 - l) ≤ x ^ l * x ^ (k - 1 - l) :=
                mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy hxy _) (pow_nonneg hx _)
            _ = x ^ (k - 1) := by rw [← pow_add, hl']
      _ = k * x ^ (k - 1) := by simp
  have hd : 0 ≤ x - y := sub_nonneg.mpr hxy
  calc (∑ l ∈ range k, x ^ l * y ^ (k - 1 - l)) * (x - y) ≤ (k * x ^ (k - 1)) * (x - y) :=
        mul_le_mul_of_nonneg_right hs hd
    _ = k * (x - y) * x ^ (k - 1) := by ring

theorem GridSum.proof : GridSum.Statement := by
  intro D i hi
  set j := D - i with hj
  have hD : i + j + 1 = D + 1 := by omega
  set F : ℝ := ((D + 1).factorial : ℝ) with hFdef
  have hF1 : (1 : ℝ) ≤ F := by
    rw [hFdef]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hF : 0 < F := lt_of_lt_of_le one_pos hF1
  have lower : ∀ n : ℕ, ((n.choose (D + 1) : ℕ) : ℝ) ≤ ∑ a ∈ range n,
      (a : ℝ) ^ i * ((n - 1 - a : ℕ) : ℝ) ^ j / ((i.factorial : ℝ) * (j.factorial : ℝ)) := by
    intro n
    have h := GridSum.choose_range n i j
    rw [hD] at h
    rw [← h, Nat.cast_sum]
    apply sum_le_sum
    intro a _
    rw [mul_div_mul_comm, Nat.cast_mul]
    exact mul_le_mul (GridSum.choose_le_pow_div_factorial _ _)
      (GridSum.choose_le_pow_div_factorial _ _) (by positivity) (by positivity)
  have upper : ∀ n : ℕ, ∑ a ∈ range n,
      (a : ℝ) ^ i * ((n - 1 - a : ℕ) : ℝ) ^ j / ((i.factorial : ℝ) * (j.factorial : ℝ)) ≤
        (((n + D).choose (D + 1) : ℕ) : ℝ) := by
    intro n
    have h := GridSum.choose_range (n + D) i j
    rw [hD] at h
    rw [← h, Nat.cast_sum]
    calc ∑ a ∈ range n,
          (a : ℝ) ^ i * ((n - 1 - a : ℕ) : ℝ) ^ j / ((i.factorial : ℝ) * (j.factorial : ℝ))
        ≤ ∑ a ∈ range n, (((a + i).choose i * (n + D - 1 - (a + i)).choose j : ℕ) : ℝ) := by
          apply sum_le_sum
          intro a ha
          have hb : n + D - 1 - (a + i) = (n - 1 - a) + j := by
            have := mem_range.mp ha; omega
          rw [hb, mul_div_mul_comm, Nat.cast_mul]
          exact mul_le_mul (GridSum.pow_div_factorial_le _ _)
            (GridSum.pow_div_factorial_le _ _) (by positivity) (by positivity)
      _ = ∑ a ∈ (range n).map (addRightEmbedding i),
            ((a.choose i * (n + D - 1 - a).choose j : ℕ) : ℝ) := by
          rw [sum_map]; rfl
      _ ≤ ∑ a ∈ range (n + D), ((a.choose i * (n + D - 1 - a).choose j : ℕ) : ℝ) := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro x hx
            rw [Finset.mem_map] at hx
            obtain ⟨a, ha, rfl⟩ := hx
            rw [mem_range] at ha ⊢
            change a + i < n + D
            omega
          · intros; positivity
  refine IsBigO.of_bound (((D + 1 : ℕ) : ℝ) * (2 * D) * 2 ^ D) ?_
  filter_upwards [eventually_ge_atTop D] with n hn
  have hL := lower n
  have hU := upper n
  set S := ∑ a ∈ range n,
      (a : ℝ) ^ i * ((n - 1 - a : ℕ) : ℝ) ^ j / ((i.factorial : ℝ) * (j.factorial : ℝ)) with hS
  have hnD : (D : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : ((n : ℝ) - D) ^ (D + 1) ≤ ((n.choose (D + 1) : ℕ) : ℝ) * F := by
    have h : (n - D) ^ (D + 1) ≤ n.choose (D + 1) * (D + 1).factorial := by
      rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
      have := Nat.pow_sub_le_descFactorial n (D + 1)
      rwa [show n + 1 - (D + 1) = n - D by omega] at this
    have h' : (((n - D : ℕ) : ℝ)) ^ (D + 1) ≤ ((n.choose (D + 1) : ℕ) : ℝ) * F := by
      rw [hFdef]; exact_mod_cast h
    rwa [Nat.cast_sub hn] at h'
  have h2 : (((n + D).choose (D + 1) : ℕ) : ℝ) * F ≤ ((n : ℝ) + D) ^ (D + 1) := by
    have h : (n + D).choose (D + 1) * (D + 1).factorial ≤ (n + D) ^ (D + 1) := by
      rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.descFactorial_le_pow _ _
    rw [hFdef]; exact_mod_cast h
  have hSlo : ((n : ℝ) - D) ^ (D + 1) / F ≤ S := by
    rw [div_le_iff₀ hF]; nlinarith
  have hShi : S ≤ ((n : ℝ) + D) ^ (D + 1) / F := by
    rw [le_div_iff₀ hF]; nlinarith
  have hy : (0 : ℝ) ≤ (n : ℝ) - D := sub_nonneg.mpr hnD
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hp1 : ((n : ℝ) - D) ^ (D + 1) ≤ (n : ℝ) ^ (D + 1) :=
    pow_le_pow_left₀ hy (by linarith) _
  have hp2 : (n : ℝ) ^ (D + 1) ≤ ((n : ℝ) + D) ^ (D + 1) :=
    pow_le_pow_left₀ (Nat.cast_nonneg n) (by linarith) _
  have hgap := GridSum.pow_sub_pow_le ((n : ℝ) + D) ((n : ℝ) - D) (D + 1) hy (by linarith)
  rw [Nat.add_sub_cancel] at hgap
  have hpow : ((n : ℝ) + D) ^ D ≤ 2 ^ D * (n : ℝ) ^ D := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have habs : |S - (n : ℝ) ^ (D + 1) / F| ≤
      ((((n : ℝ) + D) ^ (D + 1) - ((n : ℝ) - D) ^ (D + 1))) / F := by
    rw [abs_le, sub_div]
    constructor
    · have : ((n : ℝ) - D) ^ (D + 1) / F ≤ (n : ℝ) ^ (D + 1) / F := div_le_div_of_nonneg_right hp1 hF.le
      have : (n : ℝ) ^ (D + 1) / F ≤ ((n : ℝ) + D) ^ (D + 1) / F := div_le_div_of_nonneg_right hp2 hF.le
      linarith
    · have : ((n : ℝ) - D) ^ (D + 1) / F ≤ (n : ℝ) ^ (D + 1) / F := div_le_div_of_nonneg_right hp1 hF.le
      have : (n : ℝ) ^ (D + 1) / F ≤ ((n : ℝ) + D) ^ (D + 1) / F := div_le_div_of_nonneg_right hp2 hF.le
      linarith
  have hnum : 0 ≤ ((n : ℝ) + D) ^ (D + 1) - ((n : ℝ) - D) ^ (D + 1) := by linarith
  have hdiv : ((((n : ℝ) + D) ^ (D + 1) - ((n : ℝ) - D) ^ (D + 1))) / F ≤
      ((n : ℝ) + D) ^ (D + 1) - ((n : ℝ) - D) ^ (D + 1) := div_le_self hnum hF1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ D)]
  have hk : (0 : ℝ) ≤ ((D + 1 : ℕ) : ℝ) * (2 * D) := by positivity
  calc |S - (n : ℝ) ^ (D + 1) / F|
      ≤ ((n : ℝ) + D) ^ (D + 1) - ((n : ℝ) - D) ^ (D + 1) := habs.trans hdiv
    _ ≤ ((D + 1 : ℕ) : ℝ) * ((n + D) - (n - D)) * ((n : ℝ) + D) ^ D := hgap
    _ = ((D + 1 : ℕ) : ℝ) * (2 * D) * ((n : ℝ) + D) ^ D := by ring
    _ ≤ ((D + 1 : ℕ) : ℝ) * (2 * D) * (2 ^ D * (n : ℝ) ^ D) := mul_le_mul_of_nonneg_left hpow hk
    _ = ((D + 1 : ℕ) : ℝ) * (2 * D) * 2 ^ D * (n : ℝ) ^ D := by ring

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Metric Module

noncomputable section

theorem card_le_of_separated_of_norm_le {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] (s : Finset W) {lam r : ℝ} (hlam : 0 < lam) (hr : 0 ≤ r)
    (hs : ∀ x ∈ s, ‖x‖ ≤ r) (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → lam ≤ ‖x - y‖) :
    (s.card : ℝ) ≤ (1 + 2 * r / lam) ^ finrank ℝ W := by
  classical
  let _ : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  set μ : Measure W := (Module.finBasis ℝ W).addHaar with hμ
  have hl2 : 0 < lam / 2 := half_pos hlam
  have hdisj : Set.PairwiseDisjoint (s : Set W) fun w => ball w (lam / 2) := by
    intro w hw w' hw' hne
    apply ball_disjoint_ball
    rw [add_halves, dist_eq_norm]
    exact hsep w hw w' hw' hne
  have hsubset : (⋃ w ∈ s, ball w (lam / 2)) ⊆ ball (0 : W) (r + lam / 2) := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨w, hw, hxw⟩ := hx
    rw [mem_ball_zero_iff]
    rw [mem_ball, dist_eq_norm] at hxw
    calc ‖x‖ = ‖w + (x - w)‖ := by rw [add_sub_cancel]
      _ ≤ ‖w‖ + ‖x - w‖ := norm_add_le _ _
      _ < r + lam / 2 := by linarith [hs w hw]
  have hmeas := measure_biUnion_finset (μ := μ) hdisj fun w _ => measurableSet_ball
  have hle := measure_mono (μ := μ) hsubset
  rw [hmeas] at hle
  simp only [Measure.addHaar_ball_of_pos μ _ hl2, Finset.sum_const, nsmul_eq_mul] at hle
  rw [Measure.addHaar_ball_of_pos μ _ (by linarith : 0 < r + lam / 2)] at hle
  have hc0 : μ (ball 0 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hct : μ (ball 0 1) ≠ ⊤ := measure_ball_lt_top.ne
  rw [← mul_assoc] at hle
  have hle' := (ENNReal.mul_le_mul_iff_left hc0 hct).1 hle
  rw [show ((s.card : ℕ) : ENNReal) = ENNReal.ofReal (s.card : ℝ) by simp,
    ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (pow_nonneg (by linarith) _)] at hle'
  have hpos : 0 < (lam / 2) ^ finrank ℝ W := by positivity
  have key : (1 + 2 * r / lam) ^ finrank ℝ W = ((r + lam / 2) / (lam / 2)) ^ finrank ℝ W := by
    congr 1
    field_simp
    ring
  rw [key, div_pow, le_div_iff₀ hpos]
  exact hle'

theorem finrank_span_le_finrank_int {V : Type*} [AddCommGroup V] [Module ℝ V]
    (La : Submodule ℤ V) [Module.Finite ℤ La] :
    (La : Set V) ⊆ Submodule.span ℝ (La : Set V) ∧
      FiniteDimensional ℝ (Submodule.span ℝ (La : Set V)) ∧
      finrank ℝ (Submodule.span ℝ (La : Set V)) ≤ finrank ℤ La := by
  classical
  have : HasUniqueDiv V := HasUniqueDiv.of_isTorsionFree ℝ V
  have : IsAddTorsionFree V := inferInstance
  have : Module.IsTorsionFree ℤ La := inferInstance
  have : Module.Free ℤ La := Module.free_of_finite_type_torsion_free'
  let B := Module.Free.chooseBasis ℤ La
  let f : Module.Free.ChooseBasisIndex ℤ La → V := fun i => (B i : V)
  have hspan : Submodule.span ℝ (La : Set V) = Submodule.span ℝ (Set.range f) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      have hx'' : x = ∑ i, B.repr ⟨x, hx⟩ i • f i := by
        conv_lhs => rw [show x = ((⟨x, hx⟩ : La) : V) from rfl, ← B.sum_repr ⟨x, hx⟩]
        simp only [Submodule.coe_sum, Submodule.coe_smul, f]
      rw [SetLike.mem_coe, hx'']
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [← Int.cast_smul_eq_zsmul ℝ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span (B i).2
  refine ⟨Submodule.subset_span, ?_, ?_⟩
  · rw [hspan]; exact FiniteDimensional.span_of_finite ℝ (Set.finite_range f)
  · rw [hspan, finrank_eq_card_basis B]
    exact finrank_range_le_card f

theorem Packing.proof : Packing.Statement := by
  classical
  intro V _ _ La _ S b hb hmem hnorm hsep
  obtain ⟨hsub, hfd, hdim⟩ := finrank_span_le_finrank_int La
  set W := Submodule.span ℝ (La : Set V) with hW
  have hR0 : (0 : ℝ) ≤ Module.finrank ℤ La * (b + Real.log 3) := by
    have : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    positivity
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]; exact hR0
  let T : Finset W := S.subtype (· ∈ W)
  have hTcard : T.card = S.card := by
    rw [Finset.card_subtype, Finset.filter_true_of_mem]
    exact fun s hs => hsub (hmem s hs)
  have hδ : 0 < Real.exp (-b) := Real.exp_pos _
  have hbound := card_le_of_separated_of_norm_le T hδ zero_le_one
    (fun x hx => by
      rw [Finset.mem_subtype] at hx
      rw [Submodule.coe_norm]; exact hnorm _ hx)
    (fun x hx y hy hxy => by
      rw [Finset.mem_subtype] at hx hy
      rw [Submodule.coe_norm, Submodule.coe_sub]
      exact hsep _ hx _ hy (fun h => hxy (Subtype.ext h)))
  rw [hTcard] at hbound
  have hq : 1 + 2 * 1 / Real.exp (-b) ≤ 3 * Real.exp b := by
    have h1 : 1 ≤ Real.exp b := Real.one_le_exp hb
    rw [Real.exp_neg, mul_one, div_inv_eq_mul]
    linarith
  have h3 : 1 ≤ 3 * Real.exp b := by
    have h1 : 1 ≤ Real.exp b := Real.one_le_exp hb
    linarith
  have hcard : (S.card : ℝ) ≤ (3 * Real.exp b) ^ Module.finrank ℤ La :=
    hbound.trans ((pow_le_pow_left₀ (by positivity) hq _).trans (pow_le_pow_right₀ h3 hdim))
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hpos
  calc Real.log S.card ≤ Real.log ((3 * Real.exp b) ^ Module.finrank ℤ La) :=
        Real.log_le_log hSpos hcard
    _ = Module.finrank ℤ La * (b + Real.log 3) := by
        rw [Real.log_pow, Real.log_mul (by norm_num) (Real.exp_pos b).ne', Real.log_exp]
        ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def MixedKleimanTop.Statement : Prop :=
  ∀ d : ℕ, 2 ≤ d → MixedKleiman.AtDim (d - 1) → MixedKleiman.LowAt d → MixedKleiman.TopAt d

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
