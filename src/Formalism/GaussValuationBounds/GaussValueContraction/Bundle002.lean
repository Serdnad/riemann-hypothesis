module

public import Formalism.GaussValuationBounds.KapBound3
public import Formalism.GaussValuationBounds.GaussValueContraction.TruncationExponentBounds
public import Formalism.GaussValuationBounds.Statement
public import Formalism.WindowSums.PowerSeriesRelationList
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

section

namespace Formalism.NOK

theorem scaledPowMemSpanCeil : Trunc := by
  intro A _ ℓ _ hℓ X u p y M j hj hq r
  have hnum := truncationExponentBounds ℓ hℓ y M j r hj
  set c := ⌈(r : ℝ) * ℓ / ((ℓ : ℝ) - 1)⌉₊ with hc
  set σ := sigNOK ℓ y M j with hσ
  have hL : (0 : ℝ) < (ℓ : ℝ) ^ (j - 1) := by positivity
  have hℓ1 : 1 ≤ ℓ := by omega
  by_cases hry : (ℓ - 1) * r < y
  · have h1 : (r : ℝ) * ℓ / ((ℓ : ℝ) - 1) ≤ σ := by
      have h2 := hnum.2
      have h3 : ((ℓ : ℝ) - 1) * r - y - (M : ℝ) / (ℓ : ℝ) ^ (j - 1) ≤ 0 := by
        have h4 : (((ℓ - 1) * r : ℕ) : ℝ) < y := by exact_mod_cast hry
        push_cast [Nat.cast_sub hℓ1] at h4
        have h5 : (0 : ℝ) ≤ M / (ℓ : ℝ) ^ (j - 1) := by positivity
        linarith
      rw [max_eq_left h3, sub_zero] at h2
      exact h2
    have hcs : c ≤ σ := Nat.ceil_le.mpr h1
    rw [← Nat.add_sub_cancel' hcs, pow_add, mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · push_neg at hry
    obtain ⟨m, hm⟩ : ∃ m, (ℓ - 1) * r = y + m := ⟨(ℓ - 1) * r - y, by omega⟩
    have hmR : ((ℓ : ℝ) - 1) * r - y = m := by
      have h6 := congrArg (Nat.cast : ℕ → ℝ) hm
      push_cast [Nat.cast_sub hℓ1] at h6
      linarith

    have key : (ℓ : A) ^ σ * X ^ r * p (j - 1) ^ m ∈ Ideal.span {(ℓ : A) ^ c, X ^ M} := by
      obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hq
      rw [← hab, add_pow, Finset.mul_sum]
      refine Ideal.sum_mem _ fun k hk => ?_
      have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      by_cases hX : M ≤ r + ℓ ^ (j - 1) * (m - k)
      · have e : (ℓ : A) ^ σ * X ^ r * ((a * ℓ) ^ k * (b * X ^ (ℓ ^ (j - 1))) ^ (m - k) * (m.choose k : A)) =
            X ^ M * (X ^ (r + ℓ ^ (j - 1) * (m - k) - M) *
              ((ℓ : A) ^ σ * (a * ℓ) ^ k * b ^ (m - k) * (m.choose k : A))) := by
          rw [← mul_assoc (X ^ M), ← pow_add, Nat.add_sub_cancel' hX, pow_add, pow_mul]
          ring
        rw [e]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
      · have hcs : c ≤ σ + k := by
          apply Nat.ceil_le.mpr
          have h2 := hnum.2
          have h5 : ((ℓ ^ (j - 1) * (m - k) : ℕ) : ℝ) < M := by
            exact_mod_cast (by omega : ℓ ^ (j - 1) * (m - k) < M)
          push_cast [Nat.cast_sub hk'] at h5
          have h7 : (m : ℝ) - k ≤ M / (ℓ : ℝ) ^ (j - 1) := by
            rw [le_div_iff₀ hL]
            linarith [mul_comm ((ℓ : ℝ) ^ (j - 1)) ((m : ℝ) - k)]
          have hmax : max 0 (((ℓ : ℝ) - 1) * r - y - M / (ℓ : ℝ) ^ (j - 1)) ≤ k :=
            max_le (Nat.cast_nonneg _) (by rw [hmR]; linarith)
          push_cast
          linarith
        have e : (ℓ : A) ^ σ * X ^ r * ((a * ℓ) ^ k * (b * X ^ (ℓ ^ (j - 1))) ^ (m - k) * (m.choose k : A)) =
            (ℓ : A) ^ c * ((ℓ : A) ^ (σ + k - c) * (X ^ r * a ^ k * (b * X ^ (ℓ ^ (j - 1))) ^ (m - k) *
              (m.choose k : A))) := by
          rw [← mul_assoc ((ℓ : A) ^ c) ((ℓ : A) ^ (σ + k - c)), ← pow_add, Nat.add_sub_cancel' hcs]
          ring
        rw [e]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    have hj1 : j = (j - 1) + 1 := by omega
    have hprod : (∏ s ∈ Finset.range j, p s ^ (ℓ - 1)) ^ r =
        (∏ s ∈ Finset.range j, p s ^ y) * ((∏ s ∈ Finset.range (j - 1), p s ^ m) * p (j - 1) ^ m) := by
      rw [← Finset.prod_pow]
      have e1 : ∀ s, (p s ^ (ℓ - 1)) ^ r = p s ^ y * p s ^ m := fun s => by
        rw [← pow_mul, hm, pow_add]
      simp_rw [e1]
      rw [Finset.prod_mul_distrib]
      congr 1
      conv_lhs => rw [hj1]
      rw [Finset.prod_range_succ]
    have heq : (ℓ : A) ^ σ * (u * X * ∏ s ∈ Finset.range j, p s ^ (ℓ - 1)) ^ r =
        ((ℓ : A) ^ σ * X ^ r * p (j - 1) ^ m) * (∏ s ∈ Finset.range j, p s ^ y) *
          (u ^ r * ∏ s ∈ Finset.range (j - 1), p s ^ m) := by
      rw [mul_pow, mul_pow, hprod]
      ring
    rw [heq]
    refine Ideal.mul_mem_right _ _ ?_
    obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp key
    rw [← hαβ]
    exact Ideal.mem_span_pair.mpr ⟨α * ∏ s ∈ Finset.range j, p s ^ y, β, by ring⟩

end Formalism.NOK
end

section

noncomputable section

namespace Formalism.NOK

open Polynomial

theorem padicInt_valuation_unit (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ) :
    (u : ℤ_[ℓ]).valuation = 0 := by
  have h := PadicInt.valuation_mul (Units.ne_zero u) (Units.ne_zero u⁻¹)
  rw [Units.mul_inv, PadicInt.valuation_one] at h
  omega

theorem cjExist_proof : CjExist := by
  intro ℓ _ hℓ χ hχ
  have hZ := Formalism.WindowSums.arc_ZpowVal ℓ χ 1 le_rfl (fun h => absurd h hℓ) hχ
  have hℓ0 : (ℓ : ℤ_[ℓ]) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  have hdvd : ∀ j : ℤ, (ℓ : ℤ_[ℓ]) ∣ ((χ ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 := by
    intro j
    by_cases hj : j = 0
    · subst hj
      simp
    · obtain ⟨hne, hv⟩ := hZ (-j) (neg_ne_zero.2 hj)
      rw [PadicInt.unitCoeff_spec hne]
      exact Dvd.dvd.mul_left (dvd_pow_self _ (by rw [hv]; omega)) _
  choose d hd using hdvd
  have hc1 : ∀ j, -(ℓ : ℤ_[ℓ]) * (-d j) = ((χ ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 := by
    intro j
    rw [hd j]
    ring
  have key : ∀ j j' : ℤ, j ≠ j' → -d j' - -d j ≠ 0 ∧
      PadicInt.valuation (-d j' - -d j) = padicValInt ℓ (j' - j) := by
    intro j j' hjj
    have hid : χ ^ (-j) = χ ^ (-j') * χ ^ (j' - j) := by
      rw [← zpow_add]
      congr 1
      ring
    have hkey : (ℓ : ℤ_[ℓ]) ^ 1 * (-d j' - -d j) =
        ((χ ^ (-j') : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * (((χ ^ (j' - j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) := by
      have e1 := hd j
      have e2 := hd j'
      rw [hid, Units.val_mul] at e1
      linear_combination e2 - e1
    obtain ⟨hne, hv⟩ := hZ (j' - j) (sub_ne_zero.2 (Ne.symm hjj))
    have hw : -d j' - -d j ≠ 0 := by
      intro h
      rw [h, mul_zero] at hkey
      exact mul_ne_zero (Units.ne_zero _) hne hkey.symm
    refine ⟨hw, ?_⟩
    have h1 := PadicInt.valuation_p_pow_mul 1 (-d j' - -d j) hw
    rw [hkey, PadicInt.valuation_mul (Units.ne_zero _) hne, padicInt_valuation_unit, hv] at h1
    omega
  refine ⟨fun j => -d j, hc1, ?_, fun j j' h => key j' j (Ne.symm h)⟩
  have h0 : (ℓ : ℤ_[ℓ]) * d 0 = 0 := by
    rw [← hd 0]
    simp
  show -d 0 = 0
  rw [neg_eq_zero]
  exact (mul_eq_zero.1 h0).resolve_left hℓ0

end Formalism.NOK
end
end

section

namespace Formalism.NOK

theorem kapBound_proof : KapBound := by
  intro ℓ _ hℓ χ hχ ell g h a JJ hJJ hbd
  obtain ⟨hne, hval⟩ := Formalism.WindowSums.arc_KillerVal ℓ hℓ χ hχ ell JJ
  refine ⟨hne, ?_⟩

  have hcard : (JJ.erase 0).card ≤ 20 * g := by
    calc (JJ.erase 0).card ≤ JJ.card := Finset.card_le_card (Finset.erase_subset _ _)
      _ ≤ (Finset.univ.biUnion (fun t : Fin 5 => Finset.Ico (a t) (a t + 4 * (g : ℤ)))).card :=
          Finset.card_le_card hJJ
      _ ≤ ∑ t : Fin 5, (Finset.Ico (a t) (a t + 4 * (g : ℤ))).card := Finset.card_biUnion_le
      _ = ∑ t : Fin 5, 4 * g := by
          apply Finset.sum_congr rfl
          intro t _
          rw [Int.card_Ico, add_sub_cancel_left]
          omega
      _ = 20 * g := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
          ring

  have hsumv : ((∑ i ∈ JJ.erase 0, padicValInt ℓ i : ℕ) : ℝ) ≤
      5 * (4 * (g : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ (2 * (h : ℝ))) := by
    have hle : (∑ i ∈ JJ.erase 0, padicValInt ℓ i) ≤
        ∑ t : Fin 5, ∑ i ∈ (JJ.erase 0).filter (fun i => i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ))),
          padicValInt ℓ i := by
      calc (∑ i ∈ JJ.erase 0, padicValInt ℓ i)
          ≤ ∑ i ∈ JJ.erase 0, ∑ t : Fin 5,
              (if i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ)) then padicValInt ℓ i else 0) := by
            apply Finset.sum_le_sum
            intro i hi
            obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.mp (hJJ (Finset.mem_of_mem_erase hi))
            calc padicValInt ℓ i
                = (if i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ)) then padicValInt ℓ i else 0) :=
                  (if_pos ht).symm
              _ ≤ ∑ t' : Fin 5,
                    (if i ∈ Finset.Ico (a t') (a t' + 4 * (g : ℤ)) then padicValInt ℓ i else 0) :=
                  Finset.single_le_sum
                    (f := fun t' => if i ∈ Finset.Ico (a t') (a t' + 4 * (g : ℤ)) then padicValInt ℓ i else 0)
                    (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
        _ = ∑ t : Fin 5, ∑ i ∈ JJ.erase 0,
              (if i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ)) then padicValInt ℓ i else 0) :=
            Finset.sum_comm
        _ = ∑ t : Fin 5, ∑ i ∈ (JJ.erase 0).filter (fun i => i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ))),
              padicValInt ℓ i := by
            apply Finset.sum_congr rfl
            intro t _
            rw [Finset.sum_filter]
    have hwin : ∀ t : Fin 5,
        ((∑ i ∈ (JJ.erase 0).filter (fun i => i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ))),
            padicValInt ℓ i : ℕ) : ℝ) ≤ 4 * (g : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ (2 * (h : ℝ)) := by
      intro t
      have hw := Formalism.WindowSums.arc_WindowSum ℓ (a t) (4 * g) (2 * h)
        ((JJ.erase 0).filter (fun i => i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ)))) ?_ ?_ ?_
      · push_cast at hw ⊢
        exact hw
      · intro i hi
        rw [Finset.mem_filter] at hi
        push_cast
        exact hi.2
      · intro h0
        rw [Finset.mem_filter] at h0
        exact (Finset.mem_erase.mp h0.1).1 rfl
      · intro i hi
        rw [Finset.mem_filter] at hi
        push_cast
        exact hbd i (Finset.mem_of_mem_erase hi.1)
    calc ((∑ i ∈ JJ.erase 0, padicValInt ℓ i : ℕ) : ℝ)
        ≤ ((∑ t : Fin 5, ∑ i ∈ (JJ.erase 0).filter
              (fun i => i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ))), padicValInt ℓ i : ℕ) : ℝ) := by
          exact_mod_cast hle
      _ = ∑ t : Fin 5, ((∑ i ∈ (JJ.erase 0).filter
              (fun i => i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ))), padicValInt ℓ i : ℕ) : ℝ) := by
          rw [Nat.cast_sum]
      _ ≤ ∑ _t : Fin 5, (4 * (g : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ (2 * (h : ℝ))) :=
          Finset.sum_le_sum (fun t _ => hwin t)
      _ = 5 * (4 * (g : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ (2 * (h : ℝ))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num
  have hsplit : (∑ i ∈ JJ.erase 0, (1 + ell + padicValInt ℓ i)) =
      (JJ.erase 0).card * (1 + ell) + ∑ i ∈ JJ.erase 0, padicValInt ℓ i := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
  have hc : (((JJ.erase 0).card * (1 + ell) : ℕ) : ℝ) ≤ 20 * (g : ℝ) * (1 + (ell : ℝ)) := by
    have h1 : (JJ.erase 0).card * (1 + ell) ≤ 20 * g * (1 + ell) := Nat.mul_le_mul_right _ hcard
    exact_mod_cast h1
  rw [hval, hsplit]
  push_cast at hc hsumv ⊢
  linarith

end Formalism.NOK
end
