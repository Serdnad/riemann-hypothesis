module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

lemma norm_cpow_neg_le_one' {n : ℕ} (hn : 1 ≤ n) {w : ℂ} (hw : 0 ≤ w.re) : ‖(n : ℂ) ^ (-w)‖ ≤ 1 := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn)
  simp only [Complex.neg_re]
  linarith

lemma conj_natCast_cpow_neg (n : ℕ) (z : ℂ) :
    (starRingEnd ℂ) ((n : ℂ) ^ (-z)) = (n : ℂ) ^ (-(starRingEnd ℂ) z) := by
  have harg : (n : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact Real.pi_ne_zero.symm
  rw [show -(starRingEnd ℂ) z = (starRingEnd ℂ) (-z) from (map_neg _ _).symm,
    Complex.cpow_conj _ _ harg, Complex.conj_natCast]

theorem blockCountOf_statement : BlockCountOf := by
  intro hDual hPair C hC hL Q hQ Y N U J hU hJ hsmall T ρ hT
  have hU0 : (0 : ℝ) < U := Nat.cast_pos.mpr (by omega)
  have hJ0 : (0 : ℝ) < J := Nat.cast_pos.mpr (by omega)
  have hs0 : s0 = 1 - 1 / 400 := rfl
  have hQ0 : (0 : ℝ) < Q := by linarith
  set b : ℕ → ℂ := fun n => mco Y N n * (n : ℂ) ^ (-(s0 : ℂ)) with hb
  set v : PC → ℕ → ℂ := fun p n => cv p n * (n : ℂ) ^ (-(ρ p - (s0 : ℂ))) with hv
  set Δ : ℝ := (U : ℝ) + T.card * (8 * Q ^ 3) with hΔ
  have hΔ0 : 0 ≤ Δ := by positivity
  have hcv : ∀ p n, ‖cv p n‖ ≤ 1 := fun p n => DirichletCharacter.norm_le_one _ _
  have hmemn : ∀ n ∈ Ioc U (2 * U), 0 < n := fun n hn => by
    have := (Finset.mem_Ioc.mp hn).1
    omega
  have hrow : ∀ i ∈ T, ∑ j ∈ T, ‖∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v j n)‖ ≤ Δ := by
    intro i hi
    rw [← Finset.add_sum_erase T _ hi]
    have hdiag : ‖∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v i n)‖ ≤ U := by
      refine (norm_sum_le _ _).trans ?_
      have hone : ∀ n ∈ Ioc U (2 * U), ‖v i n * (starRingEnd ℂ) (v i n)‖ ≤ 1 := by
        intro n hn
        rw [norm_mul, RCLike.norm_conj]
        have h1 : ‖v i n‖ ≤ 1 := by
          simp only [hv]
          rw [norm_mul]
          have h2 : ‖(n : ℂ) ^ (-(ρ i - (s0 : ℂ)))‖ ≤ 1 := by
            refine norm_cpow_neg_le_one' (hmemn n hn) ?_
            simp only [Complex.sub_re, Complex.ofReal_re]
            linarith [(hT i hi).2.2.1]
          calc ‖cv i n‖ * ‖(n : ℂ) ^ (-(ρ i - (s0 : ℂ)))‖ ≤ 1 * 1 :=
                mul_le_mul (hcv i n) h2 (norm_nonneg _) zero_le_one
            _ = 1 := one_mul 1
        calc ‖v i n‖ * ‖v i n‖ ≤ 1 * 1 := mul_le_mul h1 h1 (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      calc ∑ n ∈ Ioc U (2 * U), ‖v i n * (starRingEnd ℂ) (v i n)‖ ≤ ∑ n ∈ Ioc U (2 * U), (1 : ℝ) :=
            Finset.sum_le_sum hone
        _ = U := by
          rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one, show 2 * U - U = U by omega]
    have hoff : ∀ j ∈ T.erase i,
        ‖∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v j n)‖ ≤ 8 * Q ^ 3 := by
      intro j hj
      obtain ⟨hji, hjT⟩ := Finset.mem_erase.mp hj
      obtain ⟨hpi, hqi, hri1, hri2, himi, -⟩ := hT i hi
      obtain ⟨hpj, hqj, hrj1, hrj2, himj, -⟩ := hT j hjT
      set w : ℂ := (ρ i - (s0 : ℂ)) + (starRingEnd ℂ) (ρ j - (s0 : ℂ)) with hw
      have hsum : ∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v j n) =
          ∑ n ∈ Ioc U (2 * U), cv i n * (starRingEnd ℂ) (cv j n) * (n : ℂ) ^ (-w) := by
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hmemn n hn).ne'
        simp only [hv, map_mul, conj_natCast_cpow_neg]
        rw [hw, show -((ρ i - (s0 : ℂ)) + (starRingEnd ℂ) (ρ j - (s0 : ℂ))) =
            -(ρ i - (s0 : ℂ)) + -(starRingEnd ℂ) (ρ j - (s0 : ℂ)) by ring, Complex.cpow_add _ _ hn0]
        ring
      have hwre : w.re = (ρ i).re - s0 + ((ρ j).re - s0) := by
        simp [hw, Complex.conj_re]
      have hwim : w.im = (ρ i).im - (ρ j).im := by
        simp [hw, Complex.conj_im]
        ring
      have hwpos : 0 < w.re := by rw [hwre]; linarith
      have hne : i ≠ j := fun h => hji h.symm
      rw [hsum]
      refine (hPair i j hpi hpj hne w hwpos U hU).trans ?_
      have hwn : ‖w‖ ≤ 1 + 2 * Q := by
        refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
        have hre : |w.re| ≤ 1 := by
          rw [abs_le, hwre]
          constructor <;> linarith
        have him : |w.im| ≤ 2 * Q := by
          rw [hwim]
          calc |(ρ i).im - (ρ j).im| ≤ |(ρ i).im| + |(ρ j).im| := abs_sub _ _
            _ ≤ 2 * Q := by linarith
        linarith
      have hqq : (((i.1 + 1) * (j.1 + 1) : ℕ) : ℝ) ≤ Q ^ 2 := by
        push_cast at hqi hqj ⊢
        rw [sq]
        exact mul_le_mul hqi hqj (by positivity) hQ0.le
      calc 2 * (((i.1 + 1) * (j.1 + 1) : ℕ) : ℝ) * (1 + ‖w‖) ≤ 2 * Q ^ 2 * (2 + 2 * Q) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hqq (by norm_num)) (by linarith)
              (by positivity) (by positivity)
        _ ≤ 8 * Q ^ 3 := by
          nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ Q by linarith) (sq_nonneg Q)]
    calc ‖∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v i n)‖ +
          ∑ j ∈ T.erase i, ‖∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v j n)‖
        ≤ U + (T.erase i).card * (8 * Q ^ 3) := by
          refine add_le_add hdiag ?_
          have := Finset.sum_le_card_nsmul _ _ _ hoff
          rwa [nsmul_eq_mul] at this
      _ ≤ Δ := by
          rw [hΔ]
          have hc : ((T.erase i).card : ℝ) ≤ T.card := by exact_mod_cast Finset.card_erase_le
          nlinarith [pow_pos hQ0 3]
  have hD := hDual PC ℕ T (Ioc U (2 * U)) b v Δ hΔ0 hrow
  have hblk : ∀ i ∈ T, ∑ n ∈ Ioc U (2 * U), b n * v i n = blk Y N U i (ρ i) := by
    intro i hi
    unfold blk
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hmemn n hn).ne'
    simp only [hb, hv]
    rw [show -ρ i = -(s0 : ℂ) + -(ρ i - (s0 : ℂ)) by ring, Complex.cpow_add _ _ hn0]
    ring
  have hbn : ∑ n ∈ Ioc U (2 * U), ‖b n‖ ^ 2 ≤ C * (U : ℝ) ^ (-(197 / 200 : ℝ)) := by
    refine le_trans (le_of_eq ?_) (hL Y N U hU)
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [hb]
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (hmemn n hn)]
    simp only [Complex.neg_re, Complex.ofReal_re]
  have hlow : (T.card : ℝ) * (1 / (2 * (J : ℝ))) ^ 2 ≤
      ∑ i ∈ T, ‖∑ n ∈ Ioc U (2 * U), b n * v i n‖ ^ 2 := by
    have := Finset.card_nsmul_le_sum T (fun i => ‖∑ n ∈ Ioc U (2 * U), b n * v i n‖ ^ 2)
      ((1 / (2 * (J : ℝ))) ^ 2) (fun i hi => by
        rw [hblk i hi]
        exact pow_le_pow_left₀ (by positivity) (hT i hi).2.2.2.2.2 2)
    rwa [nsmul_eq_mul] at this
  have hup := hD.trans (mul_le_mul_of_nonneg_right hbn hΔ0)
  have hUU : (U : ℝ) ^ (-(197 / 200 : ℝ)) * U = (U : ℝ) ^ (3 / 200 : ℝ) := by
    rw [← Real.rpow_add_one hU0.ne']
    norm_num
  have ht : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
  have hsm : (T.card : ℝ) * (8 * Q ^ 3 * (C * (U : ℝ) ^ (-(197 / 200 : ℝ)))) ≤
      T.card * (1 / (8 * (J : ℝ) ^ 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ ht
    calc 8 * Q ^ 3 * (C * (U : ℝ) ^ (-(197 / 200 : ℝ))) = 8 * Q ^ 3 * C * (U : ℝ) ^ (-(197 / 200 : ℝ)) := by
          ring
      _ ≤ _ := hsmall
  have key : (T.card : ℝ) * (1 / (2 * (J : ℝ))) ^ 2 ≤
      C * (U : ℝ) ^ (3 / 200 : ℝ) + T.card * (1 / (8 * (J : ℝ) ^ 2)) := by
    calc _ ≤ _ := hlow.trans hup
      _ = C * ((U : ℝ) ^ (-(197 / 200 : ℝ)) * U) +
            T.card * (8 * Q ^ 3 * (C * (U : ℝ) ^ (-(197 / 200 : ℝ)))) := by
          rw [hΔ]
          ring
      _ ≤ _ := by
          rw [hUU]
          linarith [hsm]
  have e1 : (T.card : ℝ) * (1 / (2 * (J : ℝ))) ^ 2 = 2 * ((T.card : ℝ) / (8 * (J : ℝ) ^ 2)) := by
    field_simp
    ring
  have e2 : (T.card : ℝ) * (1 / (8 * (J : ℝ) ^ 2)) = (T.card : ℝ) / (8 * (J : ℝ) ^ 2) := by
    rw [mul_one_div]
  rw [e1, e2] at key
  have h3 : (T.card : ℝ) / (8 * (J : ℝ) ^ 2) ≤ C * (U : ℝ) ^ (3 / 200 : ℝ) := by linarith
  rw [div_le_iff₀ (by positivity)] at h3
  calc (T.card : ℝ) ≤ C * (U : ℝ) ^ (3 / 200 : ℝ) * (8 * (J : ℝ) ^ 2) := h3
    _ = 8 * (J : ℝ) ^ 2 * C * (U : ℝ) ^ (3 / 200 : ℝ) := by ring

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end
end

section

open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

theorem duality_inequality : DualIneq := by
  intro ι κ S I b v Δ hΔ hrow
  classical
  have hz : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
    intro z
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  obtain ⟨s, hs⟩ : ∃ s : ι → ℂ, s = fun i => ∑ n ∈ I, b n * v i n := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : κ → ℂ, w = fun n => ∑ i ∈ S, (starRingEnd ℂ) (s i) * v i n := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ι → ι → ℂ, G = fun i j => ∑ n ∈ I, v i n * (starRingEnd ℂ) (v j n) :=
    ⟨_, rfl⟩
  have hs' : ∀ i, ∑ n ∈ I, b n * v i n = s i := fun i => by rw [hs]
  have hG' : ∀ i j, ∑ n ∈ I, v i n * (starRingEnd ℂ) (v j n) = G i j := fun i j => by rw [hG]
  simp_rw [hs']
  simp_rw [hG'] at hrow
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ∑ i ∈ S, ‖s i‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ∑ n ∈ I, ‖b n‖ ^ 2 := ⟨_, rfl⟩
  rw [← hX, ← hB]
  have hXnn : 0 ≤ X := by rw [hX]; positivity
  have hBnn : 0 ≤ B := by rw [hB]; positivity

  have h1 : ((X : ℝ) : ℂ) = ∑ n ∈ I, b n * w n := by
    rw [hX, Complex.ofReal_sum]
    simp_rw [hz]
    simp only [hw, Finset.mul_sum]
    conv_lhs => enter [2, i]; rw [hs]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro i _
    rw [hs]
    ring
  have h2 : X ≤ ∑ n ∈ I, ‖b n‖ * ‖w n‖ := by
    calc X = ‖((X : ℝ) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hXnn]
      _ = ‖∑ n ∈ I, b n * w n‖ := by rw [h1]
      _ ≤ ∑ n ∈ I, ‖b n * w n‖ := norm_sum_le _ _
      _ = ∑ n ∈ I, ‖b n‖ * ‖w n‖ := by simp_rw [norm_mul]
  have h3 := Finset.sum_mul_sq_le_sq_mul_sq I (fun n => ‖b n‖) (fun n => ‖w n‖)

  have hGsym : ∀ i j, ‖G i j‖ = ‖G j i‖ := by
    intro i j
    have e : G j i = (starRingEnd ℂ) (G i j) := by
      rw [hG]

      simp only [map_sum, map_mul, Complex.conj_conj]
      apply Finset.sum_congr rfl
      intro n _
      ring
    rw [e, Complex.norm_conj]
  have e : ((∑ n ∈ I, ‖w n‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, (starRingEnd ℂ) (s i) * s j * G i j := by
    conv_rhs => rw [Finset.sum_comm]
    rw [Complex.ofReal_sum]
    simp_rw [hz]

    simp only [hw, hG, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm (s := I) (t := S)]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm (s := I) (t := S)]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hle : ∑ n ∈ I, ‖w n‖ ^ 2 ≤ ∑ i ∈ S, ∑ j ∈ S, ‖s i‖ * ‖s j‖ * ‖G i j‖ := by
    have hnn : (0 : ℝ) ≤ ∑ n ∈ I, ‖w n‖ ^ 2 := by positivity
    calc ∑ n ∈ I, ‖w n‖ ^ 2 = ‖((∑ n ∈ I, ‖w n‖ ^ 2 : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hnn]
      _ = ‖∑ i ∈ S, ∑ j ∈ S, (starRingEnd ℂ) (s i) * s j * G i j‖ := by rw [e]
      _ ≤ ∑ i ∈ S, ‖∑ j ∈ S, (starRingEnd ℂ) (s i) * s j * G i j‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ S, ∑ j ∈ S, ‖s i‖ * ‖s j‖ * ‖G i j‖ := by
          apply Finset.sum_le_sum
          intro i _
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          apply Finset.sum_congr rfl
          intro j _
          rw [norm_mul, norm_mul, Complex.norm_conj]
  have hsplit : ∑ i ∈ S, ∑ j ∈ S, (‖s i‖ ^ 2 * ‖G i j‖ / 2 + ‖s j‖ ^ 2 * ‖G j i‖ / 2) =
      ∑ i ∈ S, ∑ j ∈ S, ‖s i‖ ^ 2 * ‖G i j‖ := by
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => ‖s j‖ ^ 2 * ‖G j i‖ / 2), ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hamgm : ∑ i ∈ S, ∑ j ∈ S, ‖s i‖ * ‖s j‖ * ‖G i j‖ ≤ Δ * X := by
    calc ∑ i ∈ S, ∑ j ∈ S, ‖s i‖ * ‖s j‖ * ‖G i j‖
        ≤ ∑ i ∈ S, ∑ j ∈ S, (‖s i‖ ^ 2 * ‖G i j‖ / 2 + ‖s j‖ ^ 2 * ‖G j i‖ / 2) := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          rw [← hGsym i j]
          have h0 := sq_nonneg (‖s i‖ - ‖s j‖)
          have hg := norm_nonneg (G i j)
          nlinarith
      _ = ∑ i ∈ S, ∑ j ∈ S, ‖s i‖ ^ 2 * ‖G i j‖ := hsplit
      _ = ∑ i ∈ S, ‖s i‖ ^ 2 * ∑ j ∈ S, ‖G i j‖ := by simp_rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ S, ‖s i‖ ^ 2 * Δ := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg _)
      _ = Δ * X := by rw [hX, Finset.mul_sum]; simp_rw [mul_comm]
  have hXsq : X ^ 2 ≤ B * (Δ * X) := by
    have hY : 0 ≤ ∑ n ∈ I, ‖b n‖ * ‖w n‖ := by positivity
    calc X ^ 2 ≤ (∑ n ∈ I, ‖b n‖ * ‖w n‖) ^ 2 := by nlinarith
      _ ≤ (∑ n ∈ I, ‖b n‖ ^ 2) * ∑ n ∈ I, ‖w n‖ ^ 2 := h3
      _ ≤ B * (Δ * X) := by
          rw [← hB]
          exact mul_le_mul_of_nonneg_left (hle.trans hamgm) hBnn
  rcases hXnn.eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · nlinarith

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end
end

section

open Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

attribute [local irreducible] q0 pY pJ pN in
theorem numeric_constants : Num := by
  intro C hC
  have h3 := (isLittleO_log_rpow_rpow_atTop (3 : ℝ) (by norm_num : (0 : ℝ) < 7 / 100)).bound
    (by norm_num : (0 : ℝ) < 1 / 32768)
  have h2 := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 47 / 50)).bound
    (by positivity : (0 : ℝ) < 1 / (65536 * (C + 1)))
  obtain ⟨Q1, hQ1⟩ := Filter.eventually_atTop.1 (h3.and h2)
  refine ⟨max 20 Q1, 1 + 8 * C * (1048576 : ℝ) ^ (3 / 200 : ℝ), le_max_left _ _, fun Q hQ => ?_⟩
  have hQ20 : 20 ≤ Q := (le_max_left _ _).trans hQ
  obtain ⟨hl3, hl2⟩ := hQ1 Q ((le_max_right _ _).trans hQ)
  have hQ0 : 0 < Q := by linarith
  have hlogQ : 1 ≤ Real.log Q := by
    rw [Real.le_log_iff_exp_le hQ0]
    have := Real.exp_one_lt_d9
    linarith
  have hlog0 : 0 ≤ Real.log Q := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog0 _),
    abs_of_nonneg (Real.rpow_nonneg hQ0.le _)] at hl3 hl2
  have hl3' : Real.log Q ^ 3 ≤ 1 / 32768 * Q ^ (7 / 100 : ℝ) := by
    have e : Real.log Q ^ (3 : ℝ) = Real.log Q ^ 3 := by simpa using Real.rpow_natCast (Real.log Q) 3
    rw [← e]
    exact hl3
  have hl2' : Real.log Q ^ 2 ≤ 1 / (65536 * (C + 1)) * Q ^ (47 / 50 : ℝ) := by
    have e : Real.log Q ^ (2 : ℝ) = Real.log Q ^ 2 := by simpa using Real.rpow_natCast (Real.log Q) 2
    rw [← e]
    exact hl2
  have hq1 : Q ≤ (q0 Q : ℝ) := by rw [q0]; exact Nat.le_ceil Q
  have hq2 : (q0 Q : ℝ) ≤ 2 * Q := by
    rw [q0]
    have := Nat.ceil_lt_add_one hQ0.le
    linarith
  have hqpos : 0 < q0 Q := by exact_mod_cast lt_of_lt_of_le hQ0 hq1
  have hL2 : 2 ^ Nat.log 2 (q0 Q) ≤ q0 Q := Nat.pow_log_le_self 2 hqpos.ne'
  have hJdef : pJ Q = 8 * (Nat.log 2 (q0 Q) + 1) := by rw [pJ]
  have hYdef : pY Q = q0 Q ^ 4 := by rw [pY]
  have hLr : (Nat.log 2 (q0 Q) : ℝ) * Real.log 2 ≤ Real.log Q + Real.log 2 := by
    have h1 : ((2 ^ Nat.log 2 (q0 Q) : ℕ) : ℝ) ≤ q0 Q := by exact_mod_cast hL2
    push_cast at h1
    have h4 : Real.log ((2 : ℝ) ^ Nat.log 2 (q0 Q)) ≤ Real.log (2 * Q) :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_pow, Real.log_mul (by norm_num) hQ0.ne'] at h4
    linarith
  have hlt2 := Real.log_two_gt_d9
  have hlt2' := Real.log_two_lt_d9
  have hL' : (Nat.log 2 (q0 Q) : ℝ) ≤ 3 * Real.log Q := by
    by_contra hc
    push_neg at hc
    nlinarith [(Nat.cast_nonneg (Nat.log 2 (q0 Q)) : (0 : ℝ) ≤ _)]
  have hJ : (pJ Q : ℝ) ≤ 32 * Real.log Q := by
    rw [hJdef]
    push_cast
    linarith
  have hJpos : (0 : ℝ) < pJ Q := by rw [hJdef]; positivity
  constructor
  · intro j _
    have hY : Q ^ 4 ≤ ((pY Q * 2 ^ j : ℕ) : ℝ) := by
      rw [hYdef]
      push_cast
      have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      calc Q ^ 4 ≤ (q0 Q : ℝ) ^ 4 := by gcongr
        _ ≤ (q0 Q : ℝ) ^ 4 * 2 ^ j := le_mul_of_one_le_right (by positivity) h1
    have hpow : ((pY Q * 2 ^ j : ℕ) : ℝ) ^ (-(197 / 200 : ℝ)) ≤ Q ^ (-(197 / 50 : ℝ)) := by
      calc ((pY Q * 2 ^ j : ℕ) : ℝ) ^ (-(197 / 200 : ℝ)) ≤ (Q ^ 4) ^ (-(197 / 200 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hY (by norm_num)
        _ = Q ^ (-(197 / 50 : ℝ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
            norm_num
    have hQ3 : Q ^ 3 * Q ^ (-(197 / 50 : ℝ)) = Q ^ (-(47 / 50 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hQ0]
      norm_num
    have hQ47 : Q ^ (47 / 50 : ℝ) * Q ^ (-(47 / 50 : ℝ)) = 1 := by
      rw [← Real.rpow_add hQ0]
      norm_num
    have hkey : 64 * C * (pJ Q : ℝ) ^ 2 ≤ Q ^ (47 / 50 : ℝ) := by
      have hJ2 : (pJ Q : ℝ) ^ 2 ≤ 1024 * Real.log Q ^ 2 := by nlinarith
      have hC1 : C / (C + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      calc 64 * C * (pJ Q : ℝ) ^ 2 ≤ 64 * C * (1024 * Real.log Q ^ 2) := by gcongr
        _ ≤ 64 * C * (1024 * (1 / (65536 * (C + 1)) * Q ^ (47 / 50 : ℝ))) := by gcongr
        _ = C / (C + 1) * Q ^ (47 / 50 : ℝ) := by field_simp; ring
        _ ≤ 1 * Q ^ (47 / 50 : ℝ) := by gcongr
        _ = Q ^ (47 / 50 : ℝ) := one_mul _
    rw [le_div_iff₀ (by positivity)]
    calc 8 * Q ^ 3 * C * ((pY Q * 2 ^ j : ℕ) : ℝ) ^ (-(197 / 200 : ℝ)) * (8 * (pJ Q : ℝ) ^ 2)
        ≤ 8 * Q ^ 3 * C * Q ^ (-(197 / 50 : ℝ)) * (8 * (pJ Q : ℝ) ^ 2) := by gcongr
      _ = (64 * C * (pJ Q : ℝ) ^ 2) * (Q ^ 3 * Q ^ (-(197 / 50 : ℝ))) := by ring
      _ ≤ Q ^ (47 / 50 : ℝ) * Q ^ (-(47 / 50 : ℝ)) := by rw [hQ3]; gcongr
      _ = 1 := hQ47
  · have hJ2 : (2 : ℕ) ^ pJ Q ≤ 256 * q0 Q ^ 8 := by
      rw [hJdef, pow_mul', pow_succ]
      calc (2 ^ Nat.log 2 (q0 Q) * 2) ^ 8 = 256 * (2 ^ Nat.log 2 (q0 Q)) ^ 8 := by ring
        _ ≤ 256 * q0 Q ^ 8 := by gcongr
    have hYJ : ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ≤ 1048576 * Q ^ 12 := by
      have h1 : pY Q * 2 ^ pJ Q ≤ q0 Q ^ 4 * (256 * q0 Q ^ 8) := by
        rw [hYdef]
        exact Nat.mul_le_mul_left _ hJ2
      have h4 : ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ≤ (q0 Q : ℝ) ^ 4 * (256 * (q0 Q : ℝ) ^ 8) := by
        exact_mod_cast h1
      calc ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ≤ (q0 Q : ℝ) ^ 4 * (256 * (q0 Q : ℝ) ^ 8) := h4
        _ ≤ (2 * Q) ^ 4 * (256 * (2 * Q) ^ 8) := by gcongr
        _ = 1048576 * Q ^ 12 := by ring
    have hpow : ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ^ (3 / 200 : ℝ) ≤
        (1048576 : ℝ) ^ (3 / 200 : ℝ) * Q ^ (9 / 50 : ℝ) := by
      calc ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ^ (3 / 200 : ℝ) ≤ (1048576 * Q ^ 12) ^ (3 / 200 : ℝ) :=
            Real.rpow_le_rpow (by positivity) hYJ (by norm_num)
        _ = (1048576 : ℝ) ^ (3 / 200 : ℝ) * Q ^ (9 / 50 : ℝ) := by
            rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast Q 12,
              ← Real.rpow_mul hQ0.le]
            norm_num
    have hJ3 : (pJ Q : ℝ) ^ 3 ≤ Q ^ (7 / 100 : ℝ) := by
      calc (pJ Q : ℝ) ^ 3 ≤ (32 * Real.log Q) ^ 3 := by gcongr
        _ = 32768 * Real.log Q ^ 3 := by ring
        _ ≤ 32768 * (1 / 32768 * Q ^ (7 / 100 : ℝ)) := by gcongr
        _ = Q ^ (7 / 100 : ℝ) := by ring
    have hQ14 : 1 ≤ Q ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have hsplit : Q ^ (7 / 100 : ℝ) * Q ^ (9 / 50 : ℝ) = Q ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add hQ0]
      norm_num
    calc 1 + (pJ Q : ℝ) * (8 * (pJ Q : ℝ) ^ 2 * C * ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ^ (3 / 200 : ℝ))
        = 1 + 8 * C * ((pJ Q : ℝ) ^ 3 * ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ^ (3 / 200 : ℝ)) := by ring
      _ ≤ 1 + 8 * C * (Q ^ (7 / 100 : ℝ) * ((1048576 : ℝ) ^ (3 / 200 : ℝ) * Q ^ (9 / 50 : ℝ))) := by
          gcongr
      _ = 1 + 8 * C * (1048576 : ℝ) ^ (3 / 200 : ℝ) * (Q ^ (7 / 100 : ℝ) * Q ^ (9 / 50 : ℝ)) := by ring
      _ = 1 + 8 * C * (1048576 : ℝ) ^ (3 / 200 : ℝ) * Q ^ (1 / 4 : ℝ) := by rw [hsplit]
      _ ≤ Q ^ (1 / 4 : ℝ) + 8 * C * (1048576 : ℝ) ^ (3 / 200 : ℝ) * Q ^ (1 / 4 : ℝ) := by gcongr
      _ = (1 + 8 * C * (1048576 : ℝ) ^ (3 / 200 : ℝ)) * Q ^ (1 / 4 : ℝ) := by ring

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end
end
