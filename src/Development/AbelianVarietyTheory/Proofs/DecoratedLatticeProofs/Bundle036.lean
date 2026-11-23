module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle003
public import Formalism.GaussJetBounds.GaussJetProofs.NormNatCastEqPowPadicValNat
public import Formalism.TorsionNormIteration.InverseIntegralClasses.SigmaNormLeOne
public import Formalism.TorsionNormIteration.InverseIntegralClasses.MemSpanOfNormLe
public import Formalism.TorsionNormIteration.LubinTateExample
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle032
public import Mathlib.GroupTheory.Index
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle049
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

open PowerSeries

noncomputable section

namespace GlobalTheory.Honda

theorem subst_congr_of_derivative_integral :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime → ‖(l : K)‖ < 1 →
    ∀ (f : K⟦X⟧), CoefLe 1 (PowerSeries.derivative f) → ∀ (s : Type) (A B : MvPowerSeries s K),
    MvPowerSeries.constantCoeff A = 0 → MvPowerSeries.constantCoeff B = 0 →
    (∀ m, ‖MvPowerSeries.coeff m A‖ ≤ 1) → (∀ m, ‖MvPowerSeries.coeff m B‖ ≤ 1) →
    (∀ m, ‖MvPowerSeries.coeff m (A - B)‖ ≤ ‖(l : K)‖) →
    ∀ m, ‖MvPowerSeries.coeff m (f.subst A - f.subst B)‖ ≤ ‖(l : K)‖ := by
  intro K _ _ _ l hl hlt f hf s A B hA0 hB0 hA hB hAB m
  have hsA : HasSubst A := HasSubst.of_constantCoeff_zero hA0
  have hsB : HasSubst B := HasSubst.of_constantCoeff_zero hB0

  have hterm : ∀ d : ℕ, ‖coeff d f * MvPowerSeries.coeff m (A ^ d - B ^ d)‖ ≤ ‖(l : K)‖ := by
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    have hcong := Formalism.LT.PowCongr_valid K s l hl A B hA hB 1 le_rfl
      (by intro e; simpa using hAB e) (padicValNat l d) (d / l ^ padicValNat l d) m
    have hdecomp : l ^ padicValNat l d * (d / l ^ padicValNat l d) = d :=
      Nat.mul_div_cancel' (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
    rw [hdecomp, norm_pow, pow_add, pow_one] at hcong
    have hnd : ‖(d : K)‖ = ‖(l : K)‖ ^ padicValNat l d :=
      Formalism.DworkPowerSeriesWeights.norm_natCast_eq_pow_padicValNat hl hlt hd.ne'
    have hder : ‖coeff d f‖ * ‖(d : K)‖ ≤ 1 := by
      obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
      have := hf k
      rw [coeff_derivative, norm_mul] at this
      simpa using this
    rw [norm_mul]
    calc ‖coeff d f‖ * ‖MvPowerSeries.coeff m (A ^ d - B ^ d)‖
        ≤ ‖coeff d f‖ * (‖(l : K)‖ * ‖(d : K)‖) := by
          rw [hnd]; exact mul_le_mul_of_nonneg_left hcong (norm_nonneg _)
      _ = ‖(l : K)‖ * (‖coeff d f‖ * ‖(d : K)‖) := by ring
      _ ≤ ‖(l : K)‖ * 1 := mul_le_mul_of_nonneg_left hder (norm_nonneg _)
      _ = ‖(l : K)‖ := mul_one _
  rw [map_sub, coeff_subst hsA, coeff_subst hsB,
    ← finsum_sub_distrib (coeff_subst_finite hsA f m) (coeff_subst_finite hsB f m)]
  have heq : (fun d : ℕ => coeff d f • MvPowerSeries.coeff m (A ^ d) - coeff d f • MvPowerSeries.coeff m (B ^ d))
      = fun d => coeff d f * MvPowerSeries.coeff m (A ^ d - B ^ d) := by
    funext d; rw [map_sub, smul_eq_mul, smul_eq_mul, mul_sub]
  have hfin : (Function.support fun d : ℕ => coeff d f * MvPowerSeries.coeff m (A ^ d - B ^ d)).Finite := by
    rw [← heq]
    exact ((coeff_subst_finite hsA f m).union (coeff_subst_finite hsB f m)).subset
      (Function.support_sub _ _)
  rw [heq, finsum_eq_sum _ hfin]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun d _ => hterm d

end GlobalTheory.Honda
end
end

section

open PowerSeries GlobalTheory.Honda

theorem _root_.GlobalTheory.T.subst_congr_mod_prime_of_integral_derivative : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime → ‖(l : K)‖ < 1 → ∀ (f : K⟦X⟧), CoefLe 1 (PowerSeries.derivative f) → ∀ (s : Type) (A B : MvPowerSeries s K), MvPowerSeries.constantCoeff A = 0 → MvPowerSeries.constantCoeff B = 0 → (∀ m, ‖MvPowerSeries.coeff m A‖ ≤ 1) → (∀ m, ‖MvPowerSeries.coeff m B‖ ≤ 1) → (∀ m, ‖MvPowerSeries.coeff m (A - B)‖ ≤ ‖(l : K)‖) → ∀ m, ‖MvPowerSeries.coeff m (f.subst A - f.subst B)‖ ≤ ‖(l : K)‖ := by
  intro K _ _ _ l hl hlt f hf s A B hA0 hB0 hA hB hAB m
  have hsA : HasSubst A := HasSubst.of_constantCoeff_zero hA0
  have hsB : HasSubst B := HasSubst.of_constantCoeff_zero hB0
  have hterm : ∀ d : ℕ, ‖coeff d f * MvPowerSeries.coeff m (A ^ d - B ^ d)‖ ≤ ‖(l : K)‖ := by
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    have hcong := Formalism.LT.PowCongr_valid K s l hl A B hA hB 1 le_rfl
      (by intro e; simpa using hAB e) (padicValNat l d) (d / l ^ padicValNat l d) m
    have hdecomp : l ^ padicValNat l d * (d / l ^ padicValNat l d) = d :=
      Nat.mul_div_cancel' (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
    rw [hdecomp, norm_pow, pow_add, pow_one] at hcong
    have hnd : ‖(d : K)‖ = ‖(l : K)‖ ^ padicValNat l d :=
      Formalism.DworkPowerSeriesWeights.norm_natCast_eq_pow_padicValNat hl hlt hd.ne'
    have hder : ‖coeff d f‖ * ‖(d : K)‖ ≤ 1 := by
      obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
      have := hf k
      rw [coeff_derivative, norm_mul] at this
      simpa using this
    rw [norm_mul]
    calc ‖coeff d f‖ * ‖MvPowerSeries.coeff m (A ^ d - B ^ d)‖
        ≤ ‖coeff d f‖ * (‖(l : K)‖ * ‖(d : K)‖) := by
          rw [hnd]; exact mul_le_mul_of_nonneg_left hcong (norm_nonneg _)
      _ = ‖(l : K)‖ * (‖coeff d f‖ * ‖(d : K)‖) := by ring
      _ ≤ ‖(l : K)‖ * 1 := mul_le_mul_of_nonneg_left hder (norm_nonneg _)
      _ = ‖(l : K)‖ := mul_one _
  rw [map_sub, coeff_subst hsA, coeff_subst hsB,
    ← finsum_sub_distrib (coeff_subst_finite hsA f m) (coeff_subst_finite hsB f m)]
  have heq : (fun d : ℕ => coeff d f • MvPowerSeries.coeff m (A ^ d) - coeff d f • MvPowerSeries.coeff m (B ^ d))
      = fun d => coeff d f * MvPowerSeries.coeff m (A ^ d - B ^ d) := by
    funext d; rw [map_sub, smul_eq_mul, smul_eq_mul, mul_sub]
  have hfin : (Function.support fun d : ℕ => coeff d f * MvPowerSeries.coeff m (A ^ d - B ^ d)).Finite := by
    rw [← heq]
    exact ((coeff_subst_finite hsA f m).union (coeff_subst_finite hsB f m)).subset
      (Function.support_sub _ _)
  rw [heq, finsum_eq_sum _ hfin]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun d _ => hterm d
end

section

open PowerSeries GlobalTheory.Honda

namespace GlobalTheory.Honda

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_add_pow_sub_pow_le (c e : K) {r : ℝ} (hc : ‖c‖ ≤ 1) (hce : ‖c + e‖ ≤ 1) (he : ‖e‖ ≤ r)
    (n : ℕ) : ‖(c + e) ^ n - c ^ n‖ ≤ r := by
  rw [← Commute.geom_sum₂_mul (Commute.all _ _), add_sub_cancel_left, norm_mul]
  have hs : ‖∑ k ∈ Finset.range n, (c + e) ^ k * c ^ (n - 1 - k)‖ ≤ 1 := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro k _
    rw [norm_mul, norm_pow, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hce) (by positivity) (pow_le_one₀ (norm_nonneg _) hc)
  calc _ ≤ 1 * r := mul_le_mul hs he (norm_nonneg _) zero_le_one
    _ = r := one_mul r

theorem isFrobLift_pow (l : ℕ) (σ : K →+* K) (hU : Unr K l σ) (i : ℕ) :
    Formalism.G.IsFrobLift l (l ^ i) (σ ^ i) ∧ ∀ x : K, ‖(σ ^ i) x‖ = ‖x‖ := by
  obtain ⟨_, _, hl1, hmax, hiso, hfr⟩ := hU
  induction i with
  | zero => exact ⟨fun a _ => by simp, fun x => by simp⟩
  | succ i ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨fun a ha => ?_, fun x => ?_⟩
    · rw [pow_succ', RingHom.mul_def, RingHom.comp_apply]
      set b := (σ ^ i) a
      have hb : ‖b‖ ≤ 1 := (ih2 a).le.trans ha
      have h1 : ‖σ b - b ^ l‖ ≤ ‖(l : K)‖ := hmax _ (hfr b hb)
      have hc : ‖a ^ l ^ i‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
      have h2 : ‖b ^ l - (a ^ l ^ i) ^ l‖ ≤ ‖(l : K)‖ := by
        have := norm_add_pow_sub_pow_le (a ^ l ^ i) (b - a ^ l ^ i) hc (by simpa using hb) (ih1 a ha) l
        simpa using this
      have : σ b - a ^ l ^ (i + 1) = (σ b - b ^ l) + (b ^ l - (a ^ l ^ i) ^ l) := by ring
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)
    · rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, hiso, ih2]

theorem pow_frob_sub_le : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K), Unr K l σ → ∀ (s : Type) (A : MvPowerSeries s K), (∀ m, ‖MvPowerSeries.coeff m A‖ ≤ 1) → ∀ (i : ℕ) (h : l ^ i ≠ 0) (m : s →₀ ℕ), ‖MvPowerSeries.coeff m (A ^ (l ^ i) - MvPowerSeries.expand (l ^ i) h (MvPowerSeries.map (σ ^ i) A))‖ ≤ ‖(l : K)‖ := by
  intro K _ _ _ l σ hU s A hA i h m
  have hpr : l.Prime := hU.1
  have hl1 : ‖(l : K)‖ < 1 := hU.2.2.1
  have hp0 : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr hpr.ne_zero
  exact Formalism.LT.FrobP.main l i hpr (σ ^ i) hp0 hl1 (isFrobLift_pow l σ hU i).1 A hA m

end GlobalTheory.Honda
end

section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

noncomputable section

namespace GlobalTheory.HondaFunEq

variable {K : Type} [NormedField K]

theorem sq_apply (σ : K →+* K) (a : K) : (σ ^ 2) a = σ (σ a) := by
  rw [pow_two]; rfl

theorem frobLift_sq [IsUltrametricDist K] {l : ℕ} {σ : K →+* K} (h : Unr K l σ) :
    Formalism.G.IsFrobLift l (l ^ 2) (σ ^ 2) := by
  obtain ⟨-, -, -, hmax, hiso, hfrob⟩ := h
  have key : ∀ x : K, ‖x‖ ≤ 1 → ‖σ x - x ^ l‖ ≤ ‖(l : K)‖ := fun x hx => hmax _ (hfrob x hx)
  intro a ha
  have hsa : ‖σ a‖ ≤ 1 := by rw [hiso]; exact ha
  have hal : ‖a ^ l‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
  have hd : (σ ^ 2) a - a ^ (l ^ 2) = (σ (σ a) - (σ a) ^ l) + ((σ a) ^ l - (a ^ l) ^ l) := by
    rw [sq_apply, ← pow_mul, sq]; ring
  rw [hd]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (key _ hsa) ?_)
  rw [← (Commute.all (σ a) (a ^ l)).geom_sum₂_mul, norm_mul]
  have hs : ‖∑ i ∈ Finset.range l, σ a ^ i * (a ^ l) ^ (l - 1 - i)‖ ≤ 1 :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => by
      rw [norm_mul, norm_pow, norm_pow]
      exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hsa) (by positivity) (pow_le_one₀ (norm_nonneg _) hal)
  calc _ ≤ 1 * ‖(l : K)‖ := mul_le_mul hs (key a ha) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem setting [IsUltrametricDist K] {l : ℕ} {σ : K →+* K} (h : Unr K l σ) :
    Formalism.G.FunctionalEquationSetting K l (l ^ 2) (σ ^ 2) :=
  ⟨h.1, ⟨2, by norm_num, rfl⟩, h.2.2.1, frobLift_sq h⟩

theorem coeff_ltLog_pow (l : ℕ) (hl : 2 ≤ l) (j : ℕ) :
    coeff ((l ^ 2) ^ j) (ltLog K l) = ((l : K) ^ j)⁻¹ := by
  have h : ∃ i : ℕ, (l ^ 2) ^ j = (l ^ 2) ^ i := ⟨j, rfl⟩
  simp only [ltLog, coeff_mk, dif_pos h]
  have hq : 2 ≤ l ^ 2 := le_trans hl (Nat.le_self_pow (by norm_num) l)
  have := Nat.find_spec h
  rw [(Nat.pow_right_injective hq this).symm]

theorem coeff_ltLog_of_not (l : ℕ) {n : ℕ} (h : ¬ ∃ j : ℕ, n = (l ^ 2) ^ j) :
    coeff n (ltLog K l) = 0 := by
  simp only [ltLog, coeff_mk, dif_neg h]

theorem ltLog_funEq [CharZero K] (l : ℕ) (hl : 2 ≤ l) (τ : K →+* K) :
    ltLog K l - (l : K)⁻¹ • (PowerSeries.map τ (ltLog K l)).subst ((X : K⟦X⟧) ^ (l ^ 2)) = X := by
  have hq : l ^ 2 ≠ 0 := by positivity
  have hq2 : 2 ≤ l ^ 2 := le_trans hl (Nat.le_self_pow (by norm_num) l)
  have hmap : PowerSeries.map τ (ltLog K l) = ltLog K l := by
    ext n
    simp only [coeff_map, ltLog, coeff_mk]
    split_ifs <;> simp [map_inv₀]
  rw [hmap, ← PowerSeries.expand_apply _ hq]
  ext n
  rw [map_sub, coeff_smul, PowerSeries.coeff_expand, coeff_X, smul_eq_mul]
  by_cases hn : ∃ j : ℕ, n = (l ^ 2) ^ j
  · obtain ⟨j, rfl⟩ := hn
    cases j with
    | zero =>
      have : ¬ l ^ 2 ∣ 1 := fun h => by
        have := Nat.le_of_dvd one_pos h; omega
      rw [coeff_ltLog_pow l hl 0, if_neg (by simpa using this), if_pos (pow_zero _)]; simp
    | succ k =>
      have h1 : (l ^ 2) ^ (k + 1) ≠ 1 := by
        exact (Nat.one_lt_pow (Nat.succ_ne_zero k) (by omega : 1 < l ^ 2)).ne'
      rw [if_pos (dvd_pow_self _ (Nat.succ_ne_zero k)), if_neg h1, pow_succ,
        Nat.mul_div_cancel _ (by omega), coeff_ltLog_pow l hl k, ← pow_succ, coeff_ltLog_pow l hl (k + 1)]
      have hl0 : (l : K) ≠ 0 := by exact_mod_cast (by omega : l ≠ 0)
      field_simp
      ring
  · have h1 : n ≠ 1 := fun h => hn ⟨0, by simp [h]⟩
    rw [coeff_ltLog_of_not l hn, if_neg h1]
    split_ifs with hd
    · obtain ⟨m, rfl⟩ := hd
      have : ¬ ∃ j : ℕ, m = (l ^ 2) ^ j := fun ⟨j, hj⟩ => hn ⟨j + 1, by rw [hj]; ring⟩
      rw [Nat.mul_div_cancel_left _ (by omega), coeff_ltLog_of_not l this]; simp
    · simp

theorem funEq_scaled [IsUltrametricDist K] {l : ℕ} {σ : K →+* K} {f : K⟦X⟧} {c ε : K} (hε : ‖ε‖ = 1)
    (hc : ε = c * (σ ^ 2) ε)
    (hH : CoefLe ‖(l : K)‖ (C (l : K) * f - C c * frobOp (σ ^ 2) (l ^ 2) 1 f)) (hl : (l : K) ≠ 0) :
    Formalism.G.IsFunEqType l (l ^ 2) (σ ^ 2) (ε⁻¹ • f) := by
  set τ := σ ^ 2 with hτdef
  have hq : l ^ 2 ≠ 0 := by
    have hl' : l ≠ 0 := by rintro rfl; simp at hl
    exact pow_ne_zero 2 hl'
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  have hτε : τ ε ≠ 0 := (map_ne_zero τ).2 hε0
  have hτ : τ ε⁻¹ = c * ε⁻¹ := by
    rw [map_inv₀]
    field_simp
    linear_combination hc
  have hfrob : frobOp τ (l ^ 2) 1 f = PowerSeries.expand (l ^ 2) hq (PowerSeries.map τ f) := by
    simp only [frobOp, pow_one]; rw [PowerSeries.expand_apply]
  rw [hfrob] at hH
  have hid : ε⁻¹ • f - (l : K)⁻¹ • (PowerSeries.map τ (ε⁻¹ • f)).subst ((X : K⟦X⟧) ^ (l ^ 2)) =
      (ε⁻¹ * (l : K)⁻¹) • (C (l : K) * f - C c * PowerSeries.expand (l ^ 2) hq (PowerSeries.map τ f)) := by
    rw [← PowerSeries.expand_apply _ hq, PowerSeries.smul_eq_C_mul, map_mul, map_C, map_mul,
      PowerSeries.expand_C, hτ]
    ext n
    simp only [map_sub, coeff_smul, coeff_C_mul, smul_eq_mul]
    field_simp
  intro n
  rw [hid, coeff_smul, smul_eq_mul, norm_mul, norm_mul, norm_inv, norm_inv, hε, inv_one, one_mul]
  have hlp : 0 < ‖(l : K)‖ := norm_pos_iff.2 hl
  calc ‖(l : K)‖⁻¹ * _ ≤ ‖(l : K)‖⁻¹ * ‖(l : K)‖ := mul_le_mul_of_nonneg_left (hH n) (inv_nonneg.2 hlp.le)
    _ = 1 := inv_mul_cancel₀ hlp.ne'

theorem funEqType_of_unit {p q : ℕ} (hq : q ≠ 0) {σ : K →+* K} {g : K⟦X⟧}
    (hg : Formalism.G.IsFunEqTypeMv (ι := Unit) p q hq σ (g : MvPowerSeries Unit K)) :
    Formalism.G.IsFunEqType p q σ g := by
  have hx : (PowerSeries.map σ g).subst ((X : K⟦X⟧) ^ q) =
      MvPowerSeries.expand q hq (MvPowerSeries.map σ g) := by
    rw [← PowerSeries.expand_apply q hq]
    rfl
  intro n
  have := hg (Finsupp.single () n)
  rw [← hx] at this
  exact this

theorem honda_funEq : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    Unr K l σ → ∀ (f e : K⟦X⟧), Formalism.L2.Th1.C.IsLogPair f e → ∀ c ε : K, ‖ε‖ = 1 → ε = c * (σ ^ 2) ε →
    CoefLe ‖(l : K)‖ (C (l : K) * f - C c * frobOp (σ ^ 2) (l ^ 2) 1 f) →
    CoefLe 1 (e.subst (C ε * ltLog K l)) := by
  intro K _ _ _ l σ hU f e hfe c ε hε hc hH
  have hS := setting hU
  have hl2 : 2 ≤ l := hU.2.1.le
  have hl : (l : K) ≠ 0 := by exact_mod_cast (by omega : l ≠ 0)
  have hq : l ^ 2 ≠ 0 := by positivity
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  obtain ⟨hf0, hf1, he0, hef, -⟩ := hfe
  have hg := funEq_scaled hε hc hH hl
  have hg0 : constantCoeff (ε⁻¹ • f) = 0 := by simp [hf0]
  have hαS : PowerSeries.HasSubst (ε • X : K⟦X⟧) := PowerSeries.HasSubst.smul_X' ε
  have hα0 : MvPowerSeries.constantCoeff (ε • X : K⟦X⟧) = 0 := by
    show constantCoeff (ε • X : K⟦X⟧) = 0
    simp
  have hαI : Formalism.G.IntegralMv (ε • X : K⟦X⟧) := by
    intro d
    rw [Finsupp.unique_single d]
    show ‖coeff (d ()) (ε • X : K⟦X⟧)‖ ≤ 1
    rw [coeff_smul, coeff_X, smul_eq_mul]
    split_ifs <;> simp [hε]
  have hMv := Formalism.LT.funEqSubst K l (l ^ 2) hq (σ ^ 2) hS (ε⁻¹ • f) hg0 hg Unit (ε • X : K⟦X⟧) hα0 hαI
  set ft : K⟦X⟧ := (ε⁻¹ • f).subst (ε • X : K⟦X⟧) with hft
  have hftE : Formalism.G.IsFunEqType l (l ^ 2) (σ ^ 2) ft := funEqType_of_unit hq hMv
  have hftr : ft = ε⁻¹ • rescale ε f := by
    rw [hft, PowerSeries.subst_smul hαS, PowerSeries.rescale_eq_subst]
  have hft0 : constantCoeff ft = 0 := by
    rw [hftr, ← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_rescale, coeff_zero_eq_constantCoeff_apply, hf0]
    simp
  have hft1 : coeff 1 ft = 1 := by
    rw [hftr, coeff_smul, coeff_rescale, hf1, smul_eq_mul]; field_simp
  have hL0 : constantCoeff (ltLog K l) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    apply coeff_ltLog_of_not
    rintro ⟨j, hj⟩
    exact (pow_ne_zero j hq) hj.symm
  have hLE : Formalism.G.IsFunEqType l (l ^ 2) (σ ^ 2) (ltLog K l) := by
    unfold Formalism.G.IsFunEqType
    rw [ltLog_funEq l hl2]
    intro n
    rw [coeff_X]; split_ifs <;> simp
  obtain ⟨h, hh0, hhI, hh⟩ := Formalism.LT.funEqHom K l (l ^ 2) (σ ^ 2) hS ft (ltLog K l) hft0 hft1 hftE hL0 hLE
  have hhS : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' hh0
  have hεh0 : constantCoeff (ε • h) = 0 := by simp [hh0]
  have hεhS : PowerSeries.HasSubst (ε • h) := PowerSeries.HasSubst.of_constantCoeff_zero' hεh0
  have hXh : (ε • X : K⟦X⟧).subst h = ε • h := by
    rw [PowerSeries.subst_smul hhS, PowerSeries.subst_X hhS]
  have hfεh : f.subst (ε • h) = ε • ltLog K l := by
    rw [← hh, hft, PowerSeries.subst_smul hαS, PowerSeries.subst_smul hhS,
      PowerSeries.subst_comp_subst_apply hαS hhS, hXh, smul_smul, mul_inv_cancel₀ hε0, one_smul]
  have hmain : e.subst (C ε * ltLog K l) = ε • h := by
    rw [← PowerSeries.smul_eq_C_mul, ← hfεh, ← PowerSeries.subst_comp_subst_apply
      (PowerSeries.HasSubst.of_constantCoeff_zero' hf0) hεhS, hef, PowerSeries.subst_X hεhS]
  intro n
  rw [hmain, coeff_smul, smul_eq_mul, norm_mul, hε, one_mul]
  exact hhI n

end GlobalTheory.HondaFunEq
end
end

section

open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling


theorem _root_.GlobalTheory.T.hasSum_hecke_series_spherical_eigenfunction : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ) (φ : GL (Fin n) k → ℂ), IsBorelSph k γ φ → (∀ i, γ i ≠ 0) → ∀ X : ℂ, (∀ i : Fin n, ‖(resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X‖ < 1) → ∀ g : GL (Fin n) k, HasSum (fun c : {c : GL (Fin n) k ⧸ KO k (Fin n) // (∀ i j, (c.out : GL (Fin n) k).1 i j ∈ 𝒪[k])} => X ^ (ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat * φ (g * c.1.out)) ((∏ i : Fin n, (1 - (resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X)⁻¹) * φ g) := by
  first | exact @GlobalTheory.HeckeShift.hasSum_hecke_shift | exact GlobalTheory.HeckeShift.hasSum_hecke_shift | (intros; apply GlobalTheory.HeckeShift.hasSum_hecke_shift <;> assumption)
end

section

namespace GlobalTheory

theorem relIndex_preimage_pi_eq_prod :
    ∀ {G : Type} [Group G] {r : ℕ} {H : Fin r → Type} [∀ i, Group (H i)]
      (φ : G →* ((i : Fin r) → H i)) (U U' : Subgroup G) (K J : (i : Fin r) → Subgroup (H i)),
      (∀ i, J i ≤ K i) → (∀ g ∈ U, ∀ i, φ g i ∈ K i) →
      (∀ x : (i : Fin r) → H i, (∀ i, x i ∈ K i) → ∃ g ∈ U, φ g = x) →
      (∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i, φ g i ∈ J i) →
      U'.relIndex U = ∏ i, (J i).relIndex (K i) := by
  intro G _ r H _ φ U U' K J _ hUK hsurj hU'
  let f : U →* (∀ i, K i) :=
    { toFun := fun g i => ⟨φ g i, hUK g g.2 i⟩
      map_one' := by
        funext i
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        funext i
        apply Subtype.ext
        simp }
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g, hg, hx⟩ := hsurj (fun i => (x i : H i)) (fun i => (x i).2)
    refine ⟨⟨g, hg⟩, ?_⟩
    funext i
    apply Subtype.ext
    change φ g i = _
    rw [hx]
  have hc : U'.subgroupOf U =
      (Subgroup.pi Set.univ fun i => (J i).subgroupOf (K i)).comap f := by
    ext g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, hU']
    constructor
    · rintro ⟨-, h⟩ i -
      exact Subgroup.mem_subgroupOf.2 (h i)
    · intro h
      exact ⟨g.2, fun i => Subgroup.mem_subgroupOf.1 (h i (Set.mem_univ _))⟩
  rw [Subgroup.relIndex, hc, Subgroup.index_comap_of_surjective _ hf, index_pi_univ_dep]
  rfl

end GlobalTheory
end
