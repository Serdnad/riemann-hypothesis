module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle008
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open Finset Elem

noncomputable section

theorem RestBoundOfPrimeBound.proof : RestBoundOfPrimeBound.Statement := by
  classical
  intro f r a c B₀ hf hr ha hB Q s e hp P
  set R : ℕ → ℝ := fun p => restPrimeModel f r a c Q s e p with hR
  set C : ℝ := ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)| with hC
  set X : ℝ := (restX r a : ℝ) with hXdef
  have hN2 : 2 ≤ r + a := by omega
  have hNR : (2 : ℝ) ≤ ((r + a : ℕ) : ℝ) := by exact_mod_cast hN2
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hB0 : 0 < B₀ := by nlinarith
  have hC0 : 0 ≤ C := by positivity
  have hX0 : 0 ≤ X := by
    simp only [hXdef, restX]; push_cast; positivity
  set K : ℝ := 1.5 * f * X * C with hK
  have hK0 : 0 ≤ K := by positivity
  set S : Set ℕ := {p | p ∈ P ∧ p.Prime ∧ B₀ < p} with hS
  set g : ℕ → ℝ := fun i => if i ∈ P ∧ i.Prime ∧ B₀ < i then |R i| else 0 with hg
  have hind : S.indicator (fun p => |R p|) = g := by
    funext i
    by_cases h : i ∈ P ∧ i.Prime ∧ B₀ < i
    · simp [hS, hg, Set.indicator_of_mem, h]
    · rw [Set.indicator_of_notMem (show i ∉ S from h)]
      simp [hg, h]
  have hg0 : ∀ i, 0 ≤ g i := fun i => by
    simp only [hg]; split_ifs <;> positivity
  have hgle : ∀ i, g i ≤ K * (primeWeight B₀ i / (i : ℝ) ^ 2) := fun i => by
    simp only [hg]
    split_ifs with h
    · have hw : primeWeight B₀ i = Real.log i := by simp [primeWeight, h.2.1, h.2.2]
      rw [hw]
      calc |R i| ≤ 1.5 * f * X * (Real.log i / (i : ℝ) ^ 2) * ((f * (r * a) + 1 : ℕ) : ℝ) *
            |(fibreDegree f r a c : ℝ)| := hp i h.2.1 h.2.2
        _ = K * (Real.log i / (i : ℝ) ^ 2) := by rw [hK, hC]; ring
    · exact mul_nonneg hK0 (div_nonneg (primeWeight_nonneg B₀ i) (by positivity))
  have hpart : ∀ n, ∑ i ∈ range n, g i ≤ K * (2 * Real.log 4 / B₀) := fun n => by
    calc ∑ i ∈ range n, g i ≤ ∑ i ∈ range n, K * (primeWeight B₀ i / (i : ℝ) ^ 2) :=
          Finset.sum_le_sum fun i _ => hgle i
      _ = K * ∑ i ∈ range n, primeWeight B₀ i / (i : ℝ) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ K * (2 * Real.log 4 / B₀) :=
          mul_le_mul_of_nonneg_left (prime_partial_le B₀ hB0 n) hK0
  have hgs : Summable g := summable_of_sum_range_le hg0 hpart
  have hsub : Summable (fun p : S => |R p|) :=
    (summable_subtype_iff_indicator (f := fun p : ℕ => |R p|) (s := S)).mpr (by rw [hind]; exact hgs)
  refine ⟨hsub, ?_⟩
  have htsum : ∑' p : S, |R p| ≤ K * (2 * Real.log 4 / B₀) := by
    rw [tsum_subtype S (fun p : ℕ => |R p|), hind]
    exact Real.tsum_le_of_sum_range_le hg0 hpart
  have habs : |∑' p : S, R p| ≤ ∑' p : S, |R p| := by
    have := norm_tsum_le_tsum_norm (f := fun p : S => R p)
      (by simpa [Real.norm_eq_abs] using hsub)
    simpa [Real.norm_eq_abs] using this

  have hXle : X ≤ 3 / 2 * ((r + a : ℕ) : ℝ) ^ 2 := by
    have h := XBound.intersectionNumber_baseChange r a hN2
    simp only [hXdef] at h ⊢
    linarith [h.1, h.2]
  have hNpos : (0 : ℝ) < ((r + a : ℕ) : ℝ) := by linarith
  have hD : (0 : ℝ) < 4 * f * ((r + a : ℕ) : ℝ) ^ 2 := by positivity
  have hlog : 2 * Real.log 4 / B₀ ≤ 2.78 / (4 * f * ((r + a : ℕ) : ℝ) ^ 2) := by
    calc 2 * Real.log 4 / B₀ ≤ 2.78 / B₀ :=
          div_le_div_of_nonneg_right two_log_four_le hB0.le
      _ ≤ 2.78 / (4 * f * ((r + a : ℕ) : ℝ) ^ 2) :=
          div_le_div_of_nonneg_left (by norm_num) hD hB
  have hconst := RestConstants.intersectionNumber_baseChange.2 f (r + a) hf hN2
  have hfin : K * (2 * Real.log 4 / B₀) ≤ 1.6 * C := by
    have hl0 : 0 ≤ 2 * Real.log 4 / B₀ :=
      div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))) hB0.le
    calc K * (2 * Real.log 4 / B₀)
        = (1.5 * f * X) * (2 * Real.log 4 / B₀) * C := by rw [hK]; ring
      _ ≤ (1.5 * f * (3 / 2 * ((r + a : ℕ) : ℝ) ^ 2)) * (2.78 / (4 * f * ((r + a : ℕ) : ℝ) ^ 2)) * C := by
          apply mul_le_mul_of_nonneg_right _ hC0
          apply mul_le_mul _ hlog hl0 (by positivity)
          exact mul_le_mul_of_nonneg_left hXle (by positivity)
      _ ≤ 1.6 * C := mul_le_mul_of_nonneg_right hconst hC0
  calc |∑' p : S, R p| ≤ ∑' p : S, |R p| := habs
    _ ≤ K * (2 * Real.log 4 / B₀) := htsum
    _ ≤ 1.6 * C := hfin
    _ = 1.6 * ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)| := by rw [hC]; ring

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Equiv Comb

noncomputable section

namespace CombCfBound

theorem abs_cf_perm {m : ℕ} {P : MvPolynomial (Fin m) ℚ} (hP : IsAlt P) (σ : Perm (Fin m))
    (v : Fin m → ℕ) : |cf (v ∘ σ.symm) P| = |cf v P| := by
  rw [cf_perm hP σ v, abs_mul]
  rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> simp [h]

theorem alternantPsum_cons (m q : ℕ) (ρ : List ℕ) :
    alternantPsum m (q :: ρ) = alternantPsum m ρ * psum (Fin m) ℚ q := by
  unfold alternantPsum
  simp only [List.map_cons, List.prod_cons]
  ring

theorem isAlt_alternantPsum (m : ℕ) (ρ : List ℕ) : IsAlt (alternantPsum m ρ) :=
  isAlt_vandermonde_mul_prod ρ

theorem stair_strictAnti (m : ℕ) : StrictAnti (stair m) := by
  intro i j h
  have hij : (i : ℕ) < j := h
  have := j.isLt
  simp only [stair]
  omega

theorem bound_nil (m : ℕ) (lam : Fin m → ℕ) (hlam : Antitone lam) :
    |cf (fun i => lam i + stair m i) (alternantPsum m [])| ≤ ((latticeWords 0 lam).card : ℚ) := by
  have hA : alternantPsum m [] = alt (stair m) := by
    simp [alternantPsum, vandermondeOf_X_eq_alt]
  have hl : StrictAnti (fun i => lam i + stair m i) := fun i j h =>
    Nat.add_lt_add_of_le_of_lt (hlam h.le) (stair_strictAnti m h)
  rw [hA, cf_alt_of_strictAnti hl (stair_strictAnti m)]
  split_ifs with h
  · have h0 : lam = 0 := by
      funext i
      have := congrFun h i
      show lam i = 0
      omega
    subst h0
    have hne : (latticeWords 0 (0 : Fin m → ℕ)).Nonempty := by
      refine ⟨Fin.elim0, ?_⟩
      simp only [latticeWords, mem_filter, mem_univ, true_and]
      refine ⟨fun t _ i j _ => ?_, fun i => ?_⟩
      · simp [pcnt]
      · simp [pcnt]
    rw [abs_one, Nat.one_le_cast]
    exact Finset.card_pos.mpr hne
  · simp

theorem proof (h1 : CombCfAtStair.Statement) (h2 : CombSortShift.Statement)
    (h3 : CombStripSum.Statement) : CombCfBound.Statement := by
  intro m ρ
  induction ρ with
  | nil => intro _ lam hlam; exact bound_nil m lam hlam
  | cons q ρ ih =>
    intro hpos lam hlam
    have hq : 1 ≤ q := hpos q (by simp)
    have ih' := ih (fun r hr => hpos r (List.mem_cons_of_mem _ hr))
    have hterm : ∀ i : Fin m,
        |(if q ≤ lam i + stair m i then
          cf (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q))
            (alternantPsum m ρ) else 0)| ≤
        (if q ≤ lam i + stair m i then
          |cf (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q))
            (alternantPsum m (List.replicate ρ.sum 1))| else 0) := by
      intro i
      split_ifs with hqi
      · by_cases hinj :
            Function.Injective (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q))
        · obtain ⟨σ, μ, hμ, -, hσ⟩ := h2 m lam hlam q i hqi hinj
          have hu : Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q) =
              (fun k => μ k + stair m k) ∘ σ.symm := by
            funext k
            have := hσ (σ.symm k)
            rwa [Equiv.apply_symm_apply] at this
          rw [hu, abs_cf_perm (isAlt_alternantPsum m ρ), abs_cf_perm (isAlt_alternantPsum m _),
            h1 m ρ.sum μ hμ, Nat.abs_cast]
          exact ih' μ hμ
        · simp only [Function.Injective, not_forall] at hinj
          obtain ⟨a, b, hab, hne⟩ := hinj
          rw [cf_eq_zero_of_eq (isAlt_alternantPsum m ρ) hne hab, abs_zero]
          exact abs_nonneg _
      · simp
    rw [alternantPsum_cons, cf_mul_psum]
    calc _ ≤ ∑ i : Fin m, |(if q ≤ lam i + stair m i then
          cf (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q))
            (alternantPsum m ρ) else 0)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum fun i _ => hterm i
      _ ≤ ((latticeWords (ρ.sum + q) lam).card : ℚ) := h3 m ρ.sum q lam hlam hq
      _ = ((latticeWords (q :: ρ).sum lam).card : ℚ) := by rw [List.sum_cons, add_comm]

end CombCfBound

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Equiv Comb

noncomputable section

theorem CombCfVandermondePsumOne.proof (h1 : CombCfMonomialPsumOne.Statement)
    (h2 : CombDetDescFactorial.Statement) : CombCfVandermondePsumOne.Statement := by
  intro m n l hl
  have hA : alternantPsum m (List.replicate n 1) = alt (stair m) * psum (Fin m) ℚ 1 ^ n := by
    simp only [alternantPsum, List.map_replicate, List.prod_replicate, vandermondeOf_X_eq_alt]
  have hterm : ∀ σ : Perm (Fin m),
      cf l (monomial (ex (stair m ∘ σ.symm)) (1 : ℚ) * psum (Fin m) ℚ 1 ^ n) =
        ((n.factorial : ℚ) / ∏ i, ((l i).factorial : ℚ)) *
          ∏ i, ((l i).descFactorial (stair m (σ.symm i)) : ℚ) := by
    intro σ
    rw [h1]
    have hsum : ∑ i, l i = ∑ i, (stair m ∘ σ.symm) i + n := by
      rw [hl, Function.comp_def, Equiv.sum_comp σ.symm (stair m)]
    by_cases hle : ∀ i, (stair m ∘ σ.symm) i ≤ l i
    · rw [if_pos ⟨hle, hsum⟩]
      have hd : ∀ i, ((l i).descFactorial (stair m (σ.symm i)) : ℚ) =
          ((l i).factorial : ℚ) / ((l i - stair m (σ.symm i)).factorial : ℚ) := by
        intro i
        rw [eq_div_iff (by positivity), mul_comm]
        exact_mod_cast Nat.factorial_mul_descFactorial (hle i)
      simp only [hd, Finset.prod_div_distrib, Function.comp_apply]
      have hp : (∏ i, ((l i).factorial : ℚ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i _ => by positivity
      have hq : (∏ i, ((l i - stair m (σ.symm i)).factorial : ℚ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i _ => by positivity
      field_simp
    · rw [if_neg (fun h => hle h.1)]
      push Not at hle
      obtain ⟨i, hi⟩ := hle
      simp only [Function.comp_apply] at hi
      have h0 : ∏ j, ((l j).descFactorial (stair m (σ.symm j)) : ℚ) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Nat.descFactorial_eq_zero_iff_lt.mpr hi])
      rw [h0, mul_zero]
  have hdet : ∑ σ : Perm (Fin m), ((Perm.sign σ : ℤ) : ℚ) *
      ∏ i, ((l i).descFactorial (stair m (σ.symm i)) : ℚ) = vandermondeOf (fun i => (l i : ℚ)) := by
    rw [← h2 m l, Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul, ← Equiv.prod_comp σ]
    simp
  rw [hA, alt_eq_sum, Finset.sum_mul, cf_sum]
  simp_rw [smul_mul_assoc, cf_zsmul, hterm]
  calc _ = ((n.factorial : ℚ) / ∏ i, ((l i).factorial : ℚ)) * ∑ σ : Perm (Fin m),
        ((Perm.sign σ : ℤ) : ℚ) * ∏ i, ((l i).descFactorial (stair m (σ.symm i)) : ℚ) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    _ = _ := by rw [hdet]; ring

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Comb

namespace CombCfMonomialPsumOne

theorem sum_update_sub_one {m : ℕ} (l : Fin m → ℕ) (i : Fin m) (h : 1 ≤ l i) :
    ∑ j, Function.update l i (l i - 1) j + 1 = ∑ j, l j := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i),
    Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) l]
  omega

theorem prod_factorial_update_sub_one {m : ℕ} (l v : Fin m → ℕ) (i : Fin m) (hi : v i < l i) :
    (∏ j, ((Function.update l i (l i - 1) j - v j).factorial : ℚ)) * ((l i - v i : ℕ) : ℚ) =
      ∏ j, ((l j - v j).factorial : ℚ) := by
  have hf : (fun j => ((Function.update l i (l i - 1) j - v j).factorial : ℚ)) =
      Function.update (fun j => ((l j - v j).factorial : ℚ)) i ((l i - 1 - v i).factorial : ℚ) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  rw [hf, Finset.prod_update_of_mem (Finset.mem_univ i),
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)
      (fun j => ((l j - v j).factorial : ℚ))]
  have h : l i - v i = (l i - 1 - v i) + 1 := by omega
  rw [h, Nat.factorial_succ]
  push_cast
  ring

end CombCfMonomialPsumOne


open CombCfMonomialPsumOne in
theorem CombCfMonomialPsumOne.proof : CombCfMonomialPsumOne.Statement := by
  intro m n v l
  induction n generalizing l with
  | zero =>
    rw [pow_zero, mul_one, cf_monomial]
    by_cases h : l = v
    · subst h; simp
    · rw [if_neg h, if_neg]
      rintro ⟨hle, hs⟩
      apply h
      funext i
      have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun i _ => hle i)).1
        (by simpa using hs.symm)
      exact (this i (Finset.mem_univ _)).symm
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, cf_mul_psum]
    simp only [ih]
    by_cases hC : (∀ i, v i ≤ l i) ∧ ∑ i, l i = ∑ i, v i + (n + 1)
    · rw [if_pos hC]
      obtain ⟨hle, hs⟩ := hC
      have hP : (∏ j, ((l j - v j).factorial : ℚ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun j _ => by positivity
      rw [Finset.sum_congr rfl (g := fun i => (n.factorial : ℚ) * ((l i - v i : ℕ) : ℚ) /
          ∏ j, ((l j - v j).factorial : ℚ)) ?_]
      · rw [← Finset.sum_div, ← Finset.mul_sum, ← Nat.cast_sum]
        have hsub : ∑ i, (l i - v i) + ∑ i, v i = ∑ i, l i := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hle i)
        rw [show ∑ i, (l i - v i) = n + 1 by omega, Nat.factorial_succ]
        push_cast
        ring
      · intro i _
        by_cases hi : v i < l i
        · have h1 : 1 ≤ l i := by omega
          have hle' : ∀ j, v j ≤ Function.update l i (l i - 1) j := fun j => by
            by_cases hj : j = i
            · subst hj; simp; omega
            · simp [Function.update_of_ne hj, hle j]
          have hs' := sum_update_sub_one l i h1
          rw [if_pos h1, if_pos ⟨hle', by omega⟩, ← prod_factorial_update_sub_one l v i hi]
          have hne : ((l i - v i : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : l i - v i ≠ 0)
          have hQ : (∏ j, ((Function.update l i (l i - 1) j - v j).factorial : ℚ)) ≠ 0 :=
            Finset.prod_ne_zero_iff.2 fun j _ => by positivity
          field_simp
        · have heq : l i = v i := le_antisymm (not_lt.1 hi) (hle i)
          rw [show ((l i - v i : ℕ) : ℚ) = 0 by rw [heq]; simp, mul_zero, zero_div]
          by_cases h1 : 1 ≤ l i
          · rw [if_pos h1, if_neg]
            rintro ⟨h, _⟩
            have := h i
            simp at this
            omega
          · rw [if_neg h1]
    · rw [if_neg hC]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases h1 : 1 ≤ l i
      · rw [if_pos h1]
        by_cases h2 : (∀ j, v j ≤ Function.update l i (l i - 1) j) ∧
            ∑ j, Function.update l i (l i - 1) j = ∑ j, v j + n
        · exfalso
          apply hC
          obtain ⟨hle', hs'⟩ := h2
          have hle : ∀ j, v j ≤ l j := fun j => (hle' j).trans (by
            by_cases hj : j = i
            · subst hj; simp
            · simp [Function.update_of_ne hj])
          have := sum_update_sub_one l i h1
          exact ⟨hle, by omega⟩
        · rw [if_neg h2]
      · rw [if_neg h1]

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

theorem Comb.pcnt_lt_pcnt_of_eq {m n : ℕ} (w : Fin n → Fin m) (t : Fin n) :
    pcnt w t (w t) < pcnt w n (w t) := by
  classical
  unfold pcnt
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨t, ?_, ?_⟩
    · simp
    · simp
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact ⟨lt_trans hs.1 t.2, hs.2⟩

theorem CombCellOfWordMem.proof : CombCellOfWordMem.Statement := by
  intro m lam w hw t
  classical
  have hc : ∀ i, pcnt w (youngCells lam).card i = lam i := by
    have := hw
    simp only [latticeWords, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this.2
  have hlt : pcnt w t (w t) < lam (w t) := by
    have := Comb.pcnt_lt_pcnt_of_eq w t
    rwa [hc] at this
  have hle : lam (w t) ≤ ∑ i, lam i :=
    Finset.single_le_sum (f := lam) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  simp only [youngCells, cellOfWord, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
    Finset.mem_range, true_and]
  exact ⟨lt_of_lt_of_le hlt hle, hlt⟩

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

theorem CombTableauRowCount.proof : CombTableauRowCount.Statement := by
  intro m lam T t i
  unfold pcnt rowWord
  apply Finset.card_bij' (fun s _ => T.symm s) (fun p _ => T p)
  · intro s hs
    simp only [mem_filter, mem_univ, true_and, Equiv.apply_symm_apply] at hs ⊢
    exact ⟨hs.2, hs.1⟩
  · intro p hp
    simp only [mem_filter, mem_univ, true_and, Equiv.symm_apply_apply] at hp ⊢
    exact ⟨hp.2, hp.1⟩
  · intro s _
    simp
  · intro p _
    simp

end GroundTheory.Heights₂.Heights.RestTerms
end
