module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTPiB
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DeuringHeilbronnM
public import Mathlib.RingTheory.SimpleRing.Principal
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SiegelWalfiszAPOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

def excI {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M) : ℝ :=
  match e with
  | none => 0
  | some (χ₁, _) => if χ = χ₁ then 1 else 0

def excT {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M) (y : ℝ) : ℂ :=
  match e with
  | none => 0
  | some (χ₁, β₁) => if χ = χ₁ then (y : ℂ) ^ (β₁ : ℂ) / (β₁ : ℂ) else 0

theorem mainPsi_eq {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M) (y : ℝ) :
    mainPsi e χ y = (if χ = 1 then (y : ℂ) else 0) - excT e χ y := rfl

theorem sum_excI_le {M : ℕ} [NeZero M] (e : Option (DirichletCharacter ℂ M × ℝ)) :
    ∑ χ : DirichletCharacter ℂ M, excI e χ ≤ 1 := by
  rcases e with _ | ⟨χ₁, β₁⟩
  · simp [excI]
  · have h : (∑ χ : DirichletCharacter ℂ M, excI (some (χ₁, β₁)) χ) = excI (some (χ₁, β₁)) χ₁ :=
      Finset.sum_eq_single χ₁ (fun b _ hb => if_neg hb) (fun h => absurd (Finset.mem_univ _) h)
    rw [h]
    exact (if_pos rfl).le

theorem excW_le_one {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M) (ρ : ℂ) :
    excW e χ ρ ≤ 1 := by
  rcases e with _ | ⟨χ₁, β₁⟩
  · simp [excW]
  · simp only [excW]; split_ifs <;> norm_num

theorem card_char_le (M : ℕ) [NeZero M] :
    ((Finset.univ : Finset (DirichletCharacter ℂ M)).card : ℝ) ≤ M := by
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ M]
  exact_mod_cast Nat.totient_le M

theorem sum_excW_le {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M)
    (Z : Finset ℂ) (y : ℝ) (hy : 1 ≤ y) (hZ : ∀ ρ ∈ Z, ρ.re < 1) :
    ∑ ρ ∈ Z, (excW e χ ρ : ℝ) * y ^ (ρ.re - 1) ≤ excI e χ := by
  rcases e with _ | ⟨χ₁, β₁⟩
  · simp [excW, excI]
  · simp only [excW, excI]
    by_cases h : χ = χ₁
    · simp only [h, true_and, if_true]
      have : ∀ ρ ∈ Z, (((if ρ = (β₁ : ℂ) then 1 else 0 : ℕ) : ℝ)) * y ^ (ρ.re - 1)
          = if ρ = (β₁ : ℂ) then y ^ (ρ.re - 1) else 0 := by
        intro ρ _; split_ifs <;> simp
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
      split_ifs with hm
      · exact Real.rpow_le_one_of_one_le_of_nonpos hy (by linarith [hZ _ hm])
      · norm_num
    · simp [h]

theorem excT_sub_le {M : ℕ} [NeZero M] (hM : 3 ≤ M) (e : Option (DirichletCharacter ℂ M × ℝ))
    (he : ∀ p, e = some p → IsExcPair p.1 p.2) (χ : DirichletCharacter ℂ M)
    (Z : Finset ℂ) (y κ T : ℝ) (hy : 1 ≤ y) (hT : 0 ≤ T)
    (hZ : ∀ ρ : ℂ, IsLZero χ ρ → 1 - κ / 2 ≤ ρ.re → |ρ.im| ≤ T → ρ ∈ Z) :
    ‖excT e χ y - ∑ ρ ∈ Z, (excW e χ ρ : ℂ) * (y : ℂ) ^ ρ / ρ‖ ≤ excI e χ * (2 * y * y ^ (-(κ / 2))) := by
  rcases e with _ | ⟨χ₁, β₁⟩
  · simp [excW, excI, excT]
  · obtain ⟨-, hne, hz, hlo, hhi⟩ := he _ rfl
    simp only at hne hz hlo hhi
    simp only [excW, excI, excT]
    by_cases h : χ = χ₁
    · subst h
      simp only [true_and, if_true]
      have : ∀ ρ ∈ Z, (((if ρ = (β₁ : ℂ) then 1 else 0 : ℕ) : ℂ)) * (y : ℂ) ^ ρ / ρ
          = if ρ = (β₁ : ℂ) then (y : ℂ) ^ ρ / ρ else 0 := by
        intro ρ _; split_ifs <;> simp
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
      have hy0 : 0 < y := by linarith
      split_ifs with hm
      · simp only [sub_self, norm_zero, one_mul]; positivity
      · have hb : β₁ < 1 - κ / 2 := by
          by_contra hcon
          push Not at hcon
          exact hm (hZ _ ⟨Or.inl hne, hz⟩ (by simpa using hcon) (by simpa using hT))
        have hl : 1 ≤ Real.log M := by
          rw [Real.le_log_iff_exp_le (by positivity)]
          have : (3 : ℝ) ≤ M := by exact_mod_cast hM
          linarith [Real.exp_one_lt_d9]
        have hb2 : 1 / 2 ≤ β₁ := by
          have : 1 / (8 * Real.log M) ≤ 1 / 8 := by
            apply one_div_le_one_div_of_le (by norm_num); linarith
          linarith
        rw [sub_zero, one_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.ofReal_re,
          Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        have h1 : y ^ β₁ ≤ y ^ (1 - κ / 2) := Real.rpow_le_rpow_of_exponent_le hy hb.le
        have h2 : y ^ (1 - κ / 2) = y * y ^ (-(κ / 2)) := by
          rw [sub_eq_add_neg, Real.rpow_add hy0, Real.rpow_one]
        rw [div_le_iff₀ (by linarith)]
        have h3 : 0 ≤ y * y ^ (-(κ / 2)) := by positivity
        nlinarith
    · simp [h]

theorem one_char {M : ℕ} [NeZero M] (hM : 3 ≤ M) (e : Option (DirichletCharacter ℂ M × ℝ))
    (he : ∀ p, e = some p → IsExcPair p.1 p.2) (χ : DirichletCharacter ℂ M)
    (Z : Finset ℂ) (m : ℂ → ℕ) (y κ T R : ℝ) (hy : 1 ≤ y) (hT : 0 ≤ T)
    (hZ : ∀ ρ : ℂ, IsLZero χ ρ → 1 - κ / 2 ≤ ρ.re → |ρ.im| ≤ T → ρ ∈ Z)
    (hre : ∀ ρ ∈ Z, 1 / 2 ≤ ρ.re) (hm : ∀ ρ ∈ Z, 1 ≤ m ρ)
    (hR : ‖psiChi χ y - (if χ = 1 then (y : ℂ) else 0) + ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ ρ / ρ‖ ≤ R) :
    ‖psiChi χ y - mainPsi e χ y‖ ≤
      R + 2 * y * ∑ ρ ∈ Z, ((m ρ : ℝ) - (excW e χ ρ : ℝ)) * y ^ (ρ.re - 1)
        + excI e χ * (2 * y * y ^ (-(κ / 2))) := by
  have hy0 : 0 < y := by linarith
  have e1 : psiChi χ y - mainPsi e χ y
      = (psiChi χ y - (if χ = 1 then (y : ℂ) else 0) + ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ ρ / ρ)
        - ∑ ρ ∈ Z, ((m ρ : ℂ) - (excW e χ ρ : ℂ)) * (y : ℂ) ^ ρ / ρ
        + (excT e χ y - ∑ ρ ∈ Z, (excW e χ ρ : ℂ) * (y : ℂ) ^ ρ / ρ) := by
    rw [mainPsi_eq]
    have : ∑ ρ ∈ Z, ((m ρ : ℂ) - (excW e χ ρ : ℂ)) * (y : ℂ) ^ ρ / ρ
        = ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ ρ / ρ - ∑ ρ ∈ Z, (excW e χ ρ : ℂ) * (y : ℂ) ^ ρ / ρ := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun ρ _ => by ring)
    rw [this]
    by_cases hχ : χ = 1
    · simp only [if_pos hχ]; ring
    · simp only [if_neg hχ]; ring
  have h2 : ‖∑ ρ ∈ Z, ((m ρ : ℂ) - (excW e χ ρ : ℂ)) * (y : ℂ) ^ ρ / ρ‖
      ≤ 2 * y * ∑ ρ ∈ Z, ((m ρ : ℝ) - (excW e χ ρ : ℝ)) * y ^ (ρ.re - 1) := by
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro ρ hρ
    have hw : (0 : ℝ) ≤ (m ρ : ℝ) - (excW e χ ρ : ℝ) := by
      have : ((excW e χ ρ : ℕ) : ℝ) ≤ (m ρ : ℝ) := by exact_mod_cast (excW_le_one e χ ρ).trans (hm ρ hρ)
      linarith
    have hn : ‖(m ρ : ℂ) - (excW e χ ρ : ℂ)‖ = (m ρ : ℝ) - (excW e χ ρ : ℝ) := by
      have : (m ρ : ℂ) - (excW e χ ρ : ℂ) = (((m ρ : ℝ) - (excW e χ ρ : ℝ) : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.norm_real, Real.norm_of_nonneg hw]
    have hρn : 1 / 2 ≤ ‖ρ‖ := (hre ρ hρ).trans ((le_abs_self _).trans (Complex.abs_re_le_norm ρ))
    rw [norm_div, norm_mul, hn, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    have h3 : y ^ ρ.re = y * y ^ (ρ.re - 1) := by
      rw [Real.rpow_sub hy0, Real.rpow_one]; field_simp
    rw [div_le_iff₀ (by linarith), h3]
    have h4 : 0 ≤ ((m ρ : ℝ) - (excW e χ ρ : ℝ)) * (y * y ^ (ρ.re - 1)) := by positivity
    nlinarith
  rw [e1]
  refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add hR h2)) ?_)
  exact excT_sub_le hM e he χ Z y κ T hy hT hZ

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet ArithmeticFunction

def cAP (M b n : ℕ) : ℝ := if n ≡ b [MOD M] then Λ n else 0

theorem vonMangoldtAP_nonneg (M b n : ℕ) : 0 ≤ cAP M b n := by
  unfold cAP
  split_ifs
  · exact vonMangoldt_nonneg
  · exact le_refl _

theorem vonMangoldtAP_le (M b n : ℕ) : cAP M b n ≤ Λ n := by
  unfold cAP
  split_ifs
  · exact le_refl _
  · exact vonMangoldt_nonneg

theorem sum_cAP (M b : ℕ) (t : ℝ) : ∑ n ∈ Icc 0 ⌊t⌋₊, cAP M b n = psiAP M b t := by
  unfold cAP Formalism.ZeroFreeDirichlet.psiAP
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_subset
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_Icc] at hx ⊢
    exact ⟨⟨Nat.zero_le _, hx.1.2⟩, hx.2⟩
  · intro x hx hnx
    simp only [Finset.mem_filter, Finset.mem_Icc] at hx hnx
    have hx0 : x = 0 := by
      by_contra h
      exact hnx ⟨⟨Nat.pos_of_ne_zero h, hx.1.2⟩, hx.2⟩
    subst hx0
    simp

theorem abs_piAP_sub_le (M b : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    |(piAP X M b : ℝ) - ∑ n ∈ Icc 0 ⌊X⌋₊, (Real.log n)⁻¹ * cAP M b n| ≤ 4 * √X * Real.log X := by
  have hpi : (piAP X M b : ℝ) = ∑ n ∈ Icc 0 ⌊X⌋₊, (if n.Prime ∧ n % M = b % M then (1 : ℝ) else 0) := by
    unfold piAP
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_subset (Finset.Icc_subset_Icc (by norm_num) le_rfl)
    intro n hn hn'
    have : n = 0 := by
      rw [Finset.mem_Icc] at hn hn'
      omega
    subst this
    simp [Nat.not_prime_zero]
  have hl2 := Real.log_two_gt_d9
  have hterm : ∀ n : ℕ, 0 ≤ (Real.log n)⁻¹ * cAP M b n - (if n.Prime ∧ n % M = b % M then (1 : ℝ) else 0) ∧
      (Real.log n)⁻¹ * cAP M b n - (if n.Prime ∧ n % M = b % M then (1 : ℝ) else 0) ≤
        2 * (if ¬ n.Prime then Λ n else 0) := by
    intro n
    by_cases hp : n.Prime
    · have hlog : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
      by_cases hm : n % M = b % M
      · have hm' : n ≡ b [MOD M] := hm
        simp [cAP, hp, hm, hm', vonMangoldt_apply_prime hp, hlog]
      · have hm' : ¬ n ≡ b [MOD M] := hm
        simp [cAP, hp, hm, hm']
    · simp only [hp, false_and, if_false, sub_zero, not_false_eq_true, if_true]
      rcases Nat.lt_or_ge n 2 with h2 | h2
      · have h0 : Λ n = 0 := by
          interval_cases n <;> simp
        have h0' : cAP M b n = 0 := le_antisymm (h0 ▸ vonMangoldtAP_le M b n) (vonMangoldtAP_nonneg M b n)
        simp [h0, h0']
      · have hln : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast h2)
        have hpos : 0 < Real.log n := by linarith
        have hinv : (Real.log n)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ hpos (by norm_num)]; linarith
        constructor
        · exact mul_nonneg (inv_nonneg.2 hpos.le) (vonMangoldtAP_nonneg M b n)
        · exact mul_le_mul hinv (vonMangoldtAP_le M b n) (vonMangoldtAP_nonneg M b n) (by norm_num)
  have hsum : ∑ n ∈ Icc 0 ⌊X⌋₊, (if ¬ n.Prime then Λ n else 0) = Chebyshev.psi X - Chebyshev.theta X := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Finset.sum_filter]
    symm
    apply Finset.sum_subset
    · intro n hn
      rw [Finset.mem_Ioc] at hn
      exact Finset.mem_Icc.2 ⟨by omega, hn.2⟩
    · intro n hn hn'
      have : n = 0 := by
        rw [Finset.mem_Icc] at hn
        rw [Finset.mem_Ioc] at hn'
        omega
      subst this
      simp
  have hpt := Chebyshev.psi_sub_theta_le hX
  rw [hpi, abs_sub_comm, ← Finset.sum_sub_distrib, abs_of_nonneg (Finset.sum_nonneg fun n _ => (hterm n).1)]
  calc _ ≤ ∑ n ∈ Icc 0 ⌊X⌋₊, 2 * (if ¬ n.Prime then Λ n else 0) := Finset.sum_le_sum fun n _ => (hterm n).2
    _ = 2 * (Chebyshev.psi X - Chebyshev.theta X) := by rw [← Finset.mul_sum, hsum]
    _ ≤ _ := by linarith

theorem abs_psiAP_sub_le (M : ℕ) [NeZero M] (b : ℕ) (hb : b.Coprime M) (e : Option (DirichletCharacter ℂ M × ℝ))
    (θ β t : ℝ)
    (hmain : ∑ χ : DirichletCharacter ℂ M, χ ((b : ZMod M)⁻¹) * mainPsi e χ t =
      ((t - θ * t ^ β / β : ℝ) : ℂ)) :
    |psiAP M b t - Fm (1 / (M.totient : ℝ)) θ β t| ≤
      (∑ χ : DirichletCharacter ℂ M, ‖psiChi χ t - mainPsi e χ t‖) / (M.totient : ℝ) := by
  have hφ : (0 : ℝ) < M.totient := by exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne M))
  have hid := chebyshev_progression_orthogonality M b hb t
  have h1 : (((M.totient : ℝ) * psiAP M b t - (t - θ * t ^ β / β) : ℝ) : ℂ) =
      ∑ χ : DirichletCharacter ℂ M, χ ((b : ZMod M)⁻¹) * (psiChi χ t - mainPsi e χ t) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← hid, hmain]
    push_cast
    ring
  have h2 : |(M.totient : ℝ) * psiAP M b t - (t - θ * t ^ β / β)| ≤
      ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ t - mainPsi e χ t‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, h1]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => ?_)
    rw [norm_mul]
    calc ‖χ ((b : ZMod M)⁻¹)‖ * ‖psiChi χ t - mainPsi e χ t‖ ≤ 1 * ‖psiChi χ t - mainPsi e χ t‖ := by
          gcongr
          exact χ.norm_le_one _
      _ = _ := one_mul _
  rw [le_div_iff₀ hφ]
  have h3 : (psiAP M b t - Fm (1 / (M.totient : ℝ)) θ β t) * (M.totient : ℝ) =
      (M.totient : ℝ) * psiAP M b t - (t - θ * t ^ β / β) := by
    unfold Fm
    field_simp
  calc |psiAP M b t - Fm (1 / (M.totient : ℝ)) θ β t| * (M.totient : ℝ)
      = |(psiAP M b t - Fm (1 / (M.totient : ℝ)) θ β t) * (M.totient : ℝ)| := by
        rw [abs_mul, abs_of_pos hφ]
    _ ≤ _ := by rw [h3]; exact h2

theorem mainPsi_sum_none (M : ℕ) [NeZero M] (b : ℕ) (hb : b.Coprime M) (t β : ℝ) :
    ∑ χ : DirichletCharacter ℂ M, χ ((b : ZMod M)⁻¹) * mainPsi none χ t = ((t - 0 * t ^ β / β : ℝ) : ℂ) := by
  have hu : IsUnit ((b : ZMod M)⁻¹) := by
    have h1 : IsUnit (b : ZMod M) := (ZMod.isUnit_iff_coprime b M).mpr hb
    obtain ⟨u, hu⟩ := h1
    rw [← hu, ZMod.inv_coe_unit]
    exact Units.isUnit _
  simp only [mainPsi]
  simp [Finset.sum_ite_eq', MulChar.one_apply hu]

theorem mainPsi_sum_some (M : ℕ) [NeZero M] (b : ℕ) (hb : b.Coprime M) (χ₁ : DirichletCharacter ℂ M)
    (β t : ℝ) (ht : 0 ≤ t) (hχ : χ₁ (b : ZMod M) = 1 ∨ χ₁ (b : ZMod M) = -1) :
    ∑ χ : DirichletCharacter ℂ M, χ ((b : ZMod M)⁻¹) * mainPsi (some (χ₁, β)) χ t =
      ((t - (χ₁ (b : ZMod M)).re * t ^ β / β : ℝ) : ℂ) := by
  have hbu : (b : ZMod M) * (b : ZMod M)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one b hb
  have hunit : IsUnit ((b : ZMod M)⁻¹) :=
    ⟨⟨(b : ZMod M)⁻¹, (b : ZMod M), by rw [mul_comm]; exact hbu, hbu⟩, rfl⟩
  have h1 : (1 : DirichletCharacter ℂ M) ((b : ZMod M)⁻¹) = 1 := MulChar.one_apply hunit
  have h2 : χ₁ ((b : ZMod M)⁻¹) = χ₁ (b : ZMod M) := by
    have h3 := congrArg χ₁ hbu
    rw [map_mul, map_one] at h3
    rcases hχ with h | h
    · rw [h, one_mul] at h3
      rw [h3, h]
    · rw [h] at h3 ⊢
      linear_combination -h3
  have hre : ((χ₁ (b : ZMod M)).re : ℂ) = χ₁ (b : ZMod M) := by
    rcases hχ with h | h <;> simp [h]
  simp only [mainPsi, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, h1, h2]
  push_cast
  rw [hre, Complex.ofReal_cpow ht]
  ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end
