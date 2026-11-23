module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle005
public import Formalism.LandauZeroFreeBounds.Statement
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

scoped instance (p p' : PC) : NeZero ((p.1 + 1) * (p'.1 + 1)) := ⟨by positivity⟩

def mulLevel (p p' : PC) : DirichletCharacter ℂ ((p.1 + 1) * (p'.1 + 1)) :=
  DirichletCharacter.changeLevel (dvd_mul_right (p.1 + 1) (p'.1 + 1)) p.2 *
    (DirichletCharacter.changeLevel (dvd_mul_left (p'.1 + 1) (p.1 + 1)) p'.2)⁻¹

theorem mulLevel_ne_one (p p' : PC) (hp : p.2.IsPrimitive) (hp' : p'.2.IsPrimitive) (hne : p ≠ p') :
    mulLevel p p' ≠ 1 := by
  intro h
  have h1 := mul_inv_eq_one.mp h
  have hc := congrArg DirichletCharacter.conductor h1
  rw [DirichletCharacter.conductor_changeLevel, DirichletCharacter.conductor_changeLevel,
    hp, hp'] at hc
  obtain ⟨N, χ⟩ := p
  obtain ⟨N', χ'⟩ := p'
  simp only [add_left_inj] at hc
  subst hc
  apply hne
  have := DirichletCharacter.changeLevel_injective (dvd_mul_right (N + 1) (N + 1)) h1
  exact congrArg (Sigma.mk N) this

theorem mulLevel_apply (p p' : PC) (n : ℕ) :
    mulLevel p p' (n : ZMod ((p.1 + 1) * (p'.1 + 1))) = cv p n * (starRingEnd ℂ) (cv p' n) := by
  by_cases hu : IsUnit (n : ZMod ((p.1 + 1) * (p'.1 + 1)))
  · obtain ⟨u, hu⟩ := hu
    have e1 : DirichletCharacter.changeLevel (dvd_mul_right (p.1 + 1) (p'.1 + 1)) p.2
        (n : ZMod ((p.1 + 1) * (p'.1 + 1))) = cv p n := by
      rw [← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu,
        ZMod.cast_natCast (dvd_mul_right _ _)]
      rfl
    have e2 : DirichletCharacter.changeLevel (dvd_mul_left (p'.1 + 1) (p.1 + 1)) p'.2
        (n : ZMod ((p.1 + 1) * (p'.1 + 1))) = cv p' n := by
      rw [← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu,
        ZMod.cast_natCast (dvd_mul_left _ _)]
      rfl
    have hn : ‖DirichletCharacter.changeLevel (dvd_mul_left (p'.1 + 1) (p.1 + 1)) p'.2
        (n : ZMod ((p.1 + 1) * (p'.1 + 1)))‖ = 1 := by
      rw [← hu]
      exact DirichletCharacter.unit_norm_eq_one _ u
    unfold mulLevel
    rw [MulChar.mul_apply, MulChar.inv_apply_eq_inv', e1, Complex.inv_eq_conj hn, e2]
  · rw [MulChar.map_nonunit _ hu]
    rw [ZMod.isUnit_iff_coprime] at hu
    by_cases h1 : n.Coprime (p.1 + 1)
    · have h2 : ¬ n.Coprime (p'.1 + 1) := fun h2 => hu (Nat.Coprime.mul_right h1 h2)
      have h3 : cv p' n = 0 := MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])
      rw [h3, map_zero, mul_zero]
    · have h3 : cv p n = 0 := MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])
      rw [h3, zero_mul]

private lemma sum_range_natCast_zmod_eq_sum_univ {Q : ℕ} [NeZero Q] (f : ZMod Q → ℂ) :
    ∑ n ∈ Finset.range Q, f (n : ZMod Q) = ∑ x : ZMod Q, f x := by
  refine Finset.sum_nbij (fun n : ℕ => (n : ZMod Q)) (fun _ _ => Finset.mem_univ _) ?_ ?_
    (fun _ _ => rfl)
  · intro a ha b hb hab
    have ha' : a < Q := Finset.mem_range.mp ha
    have hb' : b < Q := Finset.mem_range.mp hb
    have h := congrArg ZMod.val hab
    simp only at h
    rwa [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] at h
  · intro x _
    exact ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩

private lemma sum_range_modulus_shift_eq_zero_of_ne_one {Q : ℕ} [NeZero Q] (ψ : DirichletCharacter ℂ Q) (hψ : ψ ≠ 1) (M : ℕ) :
    ∑ n ∈ Finset.range Q, ψ ((M + n : ℕ) : ZMod Q) = 0 := by
  calc ∑ n ∈ Finset.range Q, ψ ((M + n : ℕ) : ZMod Q)
        = ∑ n ∈ Finset.range Q, (fun x => ψ ((M : ZMod Q) + x)) (n : ZMod Q) := by
          simp [Nat.cast_add]
    _ = ∑ x : ZMod Q, ψ ((M : ZMod Q) + x) := sum_range_natCast_zmod_eq_sum_univ (fun x => ψ ((M : ZMod Q) + x))
    _ = ∑ x : ZMod Q, ψ x := Equiv.sum_comp (Equiv.addLeft (M : ZMod Q)) ψ
    _ = 0 := MulChar.sum_eq_zero_of_ne_one hψ

private lemma norm_charSum_range_le_modulus_of_ne_one {Q : ℕ} [NeZero Q] (ψ : DirichletCharacter ℂ Q) (hψ : ψ ≠ 1) (M : ℕ) :
    ‖∑ n ∈ Finset.range M, ψ (n : ZMod Q)‖ ≤ (Q : ℝ) := by
  have hQ : 0 < Q := NeZero.pos Q
  refine Nat.strong_induction_on M ?_
  intro M ih
  by_cases hM : M < Q
  · calc ‖∑ n ∈ Finset.range M, ψ (n : ZMod Q)‖
          ≤ ∑ n ∈ Finset.range M, ‖ψ (n : ZMod Q)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range M, (1 : ℝ) :=
          Finset.sum_le_sum fun n _ => DirichletCharacter.norm_le_one ψ _
      _ = M := by simp
      _ ≤ Q := by exact_mod_cast hM.le
  · obtain ⟨K, hK⟩ : ∃ K, M = K + Q := ⟨M - Q, by omega⟩
    subst hK
    rw [Finset.sum_range_add, sum_range_modulus_shift_eq_zero_of_ne_one ψ hψ K, add_zero]
    exact ih K (by omega)

theorem pair_sum_bound : PairSum := by
  intro p p' hp hp' hne M
  have h := norm_charSum_range_le_modulus_of_ne_one (mulLevel p p') (mulLevel_ne_one p p' hp hp' hne) M
  simpa only [mulLevel_apply] using h

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end
end

section

open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

attribute [local irreducible] q0 pY pJ pN in
theorem final_bound_of_assembly : FinalOf := by
  rintro ⟨C, hC0, hC⟩ hDet hBC hNum
  obtain ⟨Q₀, C', hQ₀, hN⟩ := hNum C hC0
  classical

  let F : Finset PC := (range ⌈Q₀⌉₊).sigma (fun N => @Finset.univ (DirichletCharacter ℂ (N + 1)) (Fintype.ofFinite _))
  refine ⟨max C' ((F.card : ℝ) + 1), fun Q S hQ hS => ?_⟩
  have hQ14 : (1 : ℝ) ≤ Q ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hQ14' : (0 : ℝ) ≤ Q ^ (1 / 4 : ℝ) := by linarith
  rcases lt_or_ge Q Q₀ with hQQ | hQQ
  ·
    have hsub : S ⊆ F := by
      intro p hp
      obtain ⟨-, hpQ, -⟩ := hS p hp
      simp only [F, mem_sigma, mem_range, mem_univ, and_true]
      have h1 : ((p.1 : ℕ) : ℝ) < Q₀ := by push_cast at hpQ; linarith
      have h2 : (Q₀ : ℝ) ≤ (⌈Q₀⌉₊ : ℝ) := Nat.le_ceil Q₀
      exact_mod_cast h1.trans_le h2
    have hc : (S.card : ℝ) ≤ F.card := by exact_mod_cast card_le_card hsub
    calc (S.card : ℝ) ≤ (F.card : ℝ) + 1 := by linarith
      _ ≤ max C' ((F.card : ℝ) + 1) := le_max_right _ _
      _ = max C' ((F.card : ℝ) + 1) * 1 := (mul_one _).symm
      _ ≤ max C' ((F.card : ℝ) + 1) * Q ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left hQ14 (le_trans (by positivity) (le_max_right _ _))
  ·
    obtain ⟨hsm, hfin⟩ := hN Q hQQ
    have hQ20 : (20 : ℝ) ≤ Q := le_trans hQ₀ hQQ
    set J := pJ Q with hJdef
    have hJ1 : 1 ≤ J := by rw [hJdef]; unfold pJ; omega
    have hY1 : 1 ≤ pY Q := by
      unfold pY
      have : 1 ≤ q0 Q := by unfold q0; exact Nat.one_le_iff_ne_zero.mpr (by
        intro h; rw [Nat.ceil_eq_zero] at h; linarith)
      exact Nat.one_le_pow _ _ (by omega)

    have hcard := Finset.card_filter_add_card_filter_not (s := S) (fun p : PC => p.1 = 0)
    set S' := S.filter (fun p : PC => ¬ p.1 = 0) with hS'
    have h0 : (S.filter (fun p : PC => p.1 = 0)).card ≤ 1 := by
      refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
      obtain ⟨Na, χa⟩ := a
      obtain ⟨Nb, χb⟩ := b
      simp only [mem_filter] at ha hb
      obtain ⟨-, rfl⟩ := ha
      obtain ⟨-, rfl⟩ := hb
      have e1 : χa = 1 := DirichletCharacter.level_one' _ rfl
      have e2 : χb = 1 := DirichletCharacter.level_one' _ rfl
      rw [e1, e2]

    let ρ : PC → ℂ := fun p => if h : (∃ s : ℂ, 1 - 1 / 400 < s.re ∧ |s.im| ≤ Q ∧
        DirichletCharacter.LFunction p.2 s = 0) then h.choose else 0
    have hρ : ∀ p ∈ S, 1 - 1 / 400 < (ρ p).re ∧ |(ρ p).im| ≤ Q ∧ DirichletCharacter.LFunction p.2 (ρ p) = 0 := by
      intro p hp
      have h := (hS p hp).2.2
      simp only [ρ, dif_pos h]
      exact h.choose_spec
    let jf : PC → ℕ := fun p => if h : (∃ j ∈ range J, 1 / (2 * (J : ℝ)) ≤
        ‖blk (pY Q) (pN Q) (pY Q * 2 ^ j) p (ρ p)‖) then h.choose else 0
    have hne1 : ∀ p ∈ S', p.2 ≠ 1 := by
      intro p hp h
      simp only [hS', mem_filter] at hp
      have hc : p.2.conductor = p.1 + 1 := (hS p hp.1).1
      rw [h, DirichletCharacter.conductor_one] at hc
      omega
    have hjf : ∀ p ∈ S', jf p ∈ range J ∧
        1 / (2 * (J : ℝ)) ≤ ‖blk (pY Q) (pN Q) (pY Q * 2 ^ (jf p)) p (ρ p)‖ := by
      intro p hp
      have hpS : p ∈ S := (mem_filter.1 hp).1
      have hp0 : p.1 ≠ 0 := (mem_filter.1 hp).2
      obtain ⟨hprim, hlev, -⟩ := hS p hpS
      obtain ⟨h1, h2, h3⟩ := hρ p hpS
      have h := hDet Q hQ20 p hprim hp0 hlev (ρ p) (by unfold s0; exact h1) h2 h3
      rw [← hJdef] at h
      simp only [jf, dif_pos h]
      exact h.choose_spec
    have hre1 : ∀ p ∈ S', (ρ p).re < 1 := by
      intro p hp
      by_contra hc
      push Not at hc
      have hpS : p ∈ S := (mem_filter.1 hp).1
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re p.2 (Or.inl (hne1 p hp)) hc (hρ p hpS).2.2

    have hfib := Finset.card_eq_sum_card_fiberwise (f := jf) (s := S') (t := range J) (fun p hp => (hjf p hp).1)
    set K : ℕ := pY Q * 2 ^ J with hK
    have hKpos : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    have hblock : ∀ j ∈ range J, ((S'.filter (fun p => jf p = j)).card : ℝ) ≤
        8 * (J : ℝ) ^ 2 * C * (K : ℝ) ^ (3 / 200 : ℝ) := by
      intro j hj
      have hU : 1 ≤ pY Q * 2 ^ j := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by positivity))
      have h := hBC C hC0 hC Q (by linarith) (pY Q) (pN Q) (pY Q * 2 ^ j) J hU hJ1 (hsm j hj)
        (S'.filter (fun p => jf p = j)) ρ (by
          intro p hp
          obtain ⟨hpS', hpj⟩ := mem_filter.1 hp
          have hpS : p ∈ S := (mem_filter.1 hpS').1
          obtain ⟨hprim, hlev, -⟩ := hS p hpS
          obtain ⟨h1, h2, -⟩ := hρ p hpS
          refine ⟨hprim, hlev, by unfold s0; exact h1, hre1 p hpS', h2, ?_⟩
          have := (hjf p hpS').2
          rw [hpj] at this
          exact this)
      refine h.trans ?_
      have hUK : ((pY Q * 2 ^ j : ℕ) : ℝ) ≤ K := by
        have : 2 ^ j ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) (mem_range.1 hj).le
        exact_mod_cast Nat.mul_le_mul_left _ this
      have hrp : ((pY Q * 2 ^ j : ℕ) : ℝ) ^ (3 / 200 : ℝ) ≤ (K : ℝ) ^ (3 / 200 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hUK (by norm_num)
      have : (0 : ℝ) ≤ 8 * (J : ℝ) ^ 2 * C := by positivity
      exact mul_le_mul_of_nonneg_left hrp this
    have hS'card : (S'.card : ℝ) ≤ (J : ℝ) * (8 * (J : ℝ) ^ 2 * C * (K : ℝ) ^ (3 / 200 : ℝ)) := by
      rw [hfib]; push_cast
      refine (sum_le_sum hblock).trans ?_
      rw [sum_const, card_range, nsmul_eq_mul]
    have htot : (S.card : ℝ) ≤ 1 + (J : ℝ) * (8 * (J : ℝ) ^ 2 * C * (K : ℝ) ^ (3 / 200 : ℝ)) := by
      have : (S.card : ℝ) = (S.filter (fun p : PC => p.1 = 0)).card + S'.card := by
        rw [← hcard]; push_cast; ring
      rw [this]
      have : ((S.filter (fun p : PC => p.1 = 0)).card : ℝ) ≤ 1 := by exact_mod_cast h0
      linarith
    calc (S.card : ℝ) ≤ C' * Q ^ (1 / 4 : ℝ) := htot.trans hfin
      _ ≤ max C' ((F.card : ℝ) + 1) * Q ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hQ14'

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end
end

section

open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

def qd (M : ℕ) (T : ℝ) : ℕ := ⌈(M : ℝ) * T⌉₊

def pYd (M : ℕ) (T : ℝ) : ℕ := qd M T ^ 3

def pJd (M : ℕ) (T : ℝ) : ℕ := 8 * (Nat.log 2 (qd M T) + 1)

def pNd (M : ℕ) (T : ℝ) : ℕ := 2 ^ pJd M T

def blkD (Y N U : ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ n ∈ Ioc U (2 * U), mco Y N n * f n * (n : ℂ) ^ (-s)

def DivSq : Prop :=
  ∀ x : ℕ, 1 ≤ x → ∑ n ∈ Icc 1 x, ((n.divisors.card : ℕ) : ℝ) ^ 2 ≤ (x : ℝ) * (1 + Real.log x) ^ 3

def CoefficientBlockBound : Prop :=
  ∀ (Y N U : ℕ) (σ : ℝ), 1 ≤ U → 0 ≤ σ →
    ∑ n ∈ Ioc U (2 * U), (‖mco Y N n‖ * (n : ℝ) ^ (-σ)) ^ 2 ≤
      2 * (U : ℝ) ^ (1 - 2 * σ) * (1 + Real.log (2 * U)) ^ 3

def PairCross : Prop :=
  ∀ (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M), ψ ≠ 1 → ∀ w : ℂ, 0 ≤ w.re → ∀ U : ℕ, 1 ≤ U →
    ‖∑ n ∈ Ioc U (2 * U), ψ (n : ZMod M) * (n : ℂ) ^ (-w)‖ ≤ 4 * ((M : ℝ) + 1) * (1 + ‖w‖)

def PairSame : Prop :=
  ∀ (M : ℕ) [NeZero M] (w : ℂ), 0 ≤ w.re → w.re ≤ 1 → w.im ≠ 0 → ∀ U : ℕ, 1 ≤ U →
    ‖∑ n ∈ Ioc U (2 * U), (1 : DirichletCharacter ℂ M) (n : ZMod M) * (n : ℂ) ^ (-w)‖ ≤
      4 * (U : ℝ) ^ (1 - w.re) / |w.im| + 4 * ((M : ℝ) + 1) * (1 + ‖w‖)

def Spacing : Prop :=
  ∀ (P : Finset ℝ) (T : ℝ), 0 ≤ T → (∀ x ∈ P, |x| ≤ T) → (∀ x ∈ P, ∀ y ∈ P, x ≠ y → 1 ≤ |x - y|) →
    (P.card : ℝ) ≤ 2 * T + 1 ∧ ∀ t ∈ P, ∑ x ∈ P.erase t, 1 / |t - x| ≤ 2 * (1 + Real.log (2 * T + 1))

def Triv : Prop :=
  ∀ (M : ℕ) [NeZero M] (T : ℝ) (S : Finset (DirichletCharacter ℂ M × ℂ)), 0 ≤ T →
    (∀ p ∈ S, |p.2.im| ≤ T) → (∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → p.1 = p'.1 → 1 ≤ |p.2.im - p'.2.im|) →
    (S.card : ℝ) ≤ (M : ℝ) * (2 * T + 1)

def Offdiag : Prop :=
  ∀ (M : ℕ) [NeZero M] (S : Finset (DirichletCharacter ℂ M × ℂ)) (σ T : ℝ) (U : ℕ), 1 ≤ U → 2 ≤ T →
    1 / 2 ≤ σ → (∀ p ∈ S, σ ≤ p.2.re ∧ p.2.re ≤ 1 ∧ |p.2.im| ≤ T) →
    (∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → p.1 = p'.1 → 1 ≤ |p.2.im - p'.2.im|) →
    ∀ p ∈ S, ∑ p' ∈ S, ‖∑ n ∈ Ioc U (2 * U), p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) *
        (n : ℂ) ^ (-((p.2 - (σ : ℂ)) + (starRingEnd ℂ) (p'.2 - (σ : ℂ))))‖ ≤
      (U : ℝ) * (9 + 8 * Real.log (2 * T + 1)) + (S.card : ℝ) * (8 * ((M : ℝ) + 1) * (2 + 2 * T))

def BlockCnt : Prop :=
  ∀ {α : Type} (S : Finset α) (f : α → ℕ → ℂ) (ρ : α → ℂ) (Y N U : ℕ) (σ θ G K : ℝ), 1 ≤ U → 0 < θ →
    0 ≤ σ → 0 ≤ G → 0 ≤ K →
    (∀ p ∈ S, ∀ n : ℕ, ‖f p n‖ ≤ 1) → (∀ p ∈ S, σ ≤ (ρ p).re) →
    (∀ p ∈ S, ∑ p' ∈ S, ‖∑ n ∈ Ioc U (2 * U), f p n * (starRingEnd ℂ) (f p' n) *
        (n : ℂ) ^ (-((ρ p - (σ : ℂ)) + (starRingEnd ℂ) (ρ p' - (σ : ℂ))))‖ ≤ (U : ℝ) * G + (S.card : ℝ) * K) →
    (∀ p ∈ S, θ ≤ ‖blkD Y N U (f p) (ρ p)‖) →
    2 * (U : ℝ) ^ (1 - 2 * σ) * (1 + Real.log (2 * U)) ^ 3 * K ≤ θ ^ 2 / 2 →
    (S.card : ℝ) ≤ 4 * (U : ℝ) ^ (2 - 2 * σ) * (1 + Real.log (2 * U)) ^ 3 * G / θ ^ 2

def EtaPartial : Prop :=
  ∀ s : ℂ, 0 < s.re → s ≠ 1 → ∀ N : ℕ, 1 ≤ N →
    ‖(1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s -
        (∑ n ∈ Icc 1 (2 * N), (n : ℂ) ^ (-s) - (2 : ℂ) ^ (1 - s) * ∑ n ∈ Icc 1 N, (n : ℂ) ^ (-s))‖ ≤
      4 * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re)

def PrincipalZeta : Prop :=
  ∀ (M : ℕ) [NeZero M] (s : ℂ), 0 < s.re → IsLZero (1 : DirichletCharacter ℂ M) s → riemannZeta s = 0

def Detect1 : Prop :=
  ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M), χ ≠ 1 → ∀ T : ℝ, 2 ≤ T → 3 ≤ M →
    ∀ ρ : ℂ, 3 / 4 ≤ ρ.re → |ρ.im| ≤ T → DirichletCharacter.LFunction χ ρ = 0 →
      ∃ j ∈ range (pJd M T), 1 / (2 * (pJd M T : ℝ)) ≤
        ‖blkD (pYd M T) (pNd M T) (pYd M T * 2 ^ j) (fun n => χ (n : ZMod M)) ρ‖

def Detect0 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ (M : ℕ) [NeZero M] (T : ℝ), 2 ≤ T → 3 ≤ M → q₀ ≤ qd M T →
    ∀ ρ : ℂ, 3 / 4 ≤ ρ.re → |ρ.im| ≤ T → IsLZero (1 : DirichletCharacter ℂ M) ρ →
      ∃ i ∈ range 2, ∃ j ∈ range (pJd M T + 1),
        c / (((pJd M T : ℝ) + 1) * Real.log (qd M T)) ≤
          ‖blkD (pYd M T) (2 ^ i * pNd M T) (pYd M T * 2 ^ j)
            (fun n => (1 : DirichletCharacter ℂ 1) (n : ZMod 1)) ρ‖

def Count1 : Prop :=
  ∃ C : ℝ, ∃ q₀ : ℕ, ∀ (M : ℕ) [NeZero M] (T σ : ℝ) (S : Finset (DirichletCharacter ℂ M × ℂ)),
    3 ≤ M → 2 ≤ T → 3 / 4 ≤ σ → q₀ ≤ qd M T →
    (∀ p ∈ S, p.1 ≠ 1 ∧ σ ≤ p.2.re ∧ p.2.re < 1 ∧ |p.2.im| ≤ T ∧ DirichletCharacter.LFunction p.1 p.2 = 0) →
    (∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → p.1 = p'.1 → 1 ≤ |p.2.im - p'.2.im|) →
    (S.card : ℝ) ≤ C * ((M : ℝ) * T) ^ (24 * (1 - σ)) * Real.log ((M : ℝ) * T) ^ 10

def Count0 : Prop :=
  ∃ C : ℝ, ∃ q₀ : ℕ, ∀ (M : ℕ) [NeZero M] (T σ : ℝ) (S : Finset (DirichletCharacter ℂ M × ℂ)),
    3 ≤ M → 2 ≤ T → 3 / 4 ≤ σ → q₀ ≤ qd M T →
    (∀ p ∈ S, p.1 = 1 ∧ σ ≤ p.2.re ∧ p.2.re < 1 ∧ |p.2.im| ≤ T ∧ IsLZero p.1 p.2) →
    (∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → 1 ≤ |p.2.im - p'.2.im|) →
    (S.card : ℝ) ≤ C * ((M : ℝ) * T) ^ (24 * (1 - σ)) * Real.log ((M : ℝ) * T) ^ 10

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end

section

open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

private lemma intervalIntegrable_inv_log_two {Y : ℝ} (hY : 2 ≤ Y) :
    IntervalIntegrable (fun t => 1 / Real.log t) MeasureTheory.volume 2 Y := by
  apply ContinuousOn.intervalIntegrable
  refine continuousOn_const.div (Real.continuousOn_log.mono ?_) ?_
  · intro t ht
    rw [Set.uIcc_of_le hY] at ht
    exact Set.mem_compl_singleton_iff.2 (by linarith [ht.1] : (0 : ℝ) < t).ne'
  · intro t ht
    rw [Set.uIcc_of_le hY] at ht
    exact (Real.log_pos (by linarith [ht.1])).ne'

theorem liX_upper {Y : ℝ} (hY : 2 ≤ Y) : 0 ≤ liX Y ∧ liX Y ≤ 2 * Y := by
  have hpos : ∀ t ∈ Set.Icc (2 : ℝ) Y, 0 < Real.log t := fun t ht => Real.log_pos (by linarith [ht.1])
  have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  constructor
  · unfold liX
    exact intervalIntegral.integral_nonneg hY (fun t ht => (one_div_pos.2 (hpos t ht)).le)
  · unfold liX
    calc ∫ t in (2 : ℝ)..Y, 1 / Real.log t ≤ ∫ t in (2 : ℝ)..Y, (2 : ℝ) := by
          apply intervalIntegral.integral_mono_on hY (intervalIntegrable_inv_log_two hY) intervalIntegrable_const
          intro t ht
          have h1 : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht.1
          rw [div_le_iff₀ (hpos t ht)]
          linarith
      _ = (Y - 2) * 2 := by simp
      _ ≤ 2 * Y := by linarith

theorem liX_lower {X : ℝ} (hX : 4 ≤ X) : X / (2 * Real.log X) ≤ liX X := by
  have hX2 : (2 : ℝ) ≤ X := by linarith
  have hLX : 0 < Real.log X := Real.log_pos (by linarith)
  have hmono : ∫ t in (2 : ℝ)..X, 1 / Real.log X ≤ liX X := by
    unfold liX
    apply intervalIntegral.integral_mono_on hX2 intervalIntegrable_const (intervalIntegrable_inv_log_two hX2)
    intro t ht
    have ht0 : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    exact one_div_le_one_div_of_le ht0 (Real.log_le_log (by linarith [ht.1]) ht.2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  refine le_trans ?_ hmono
  rw [mul_one_div, div_le_div_iff₀ (by linarith) hLX]
  nlinarith [mul_le_mul_of_nonneg_right hX hLX.le]

theorem liX_pow_le {X β δ : ℝ} (hX : 4 ≤ X) (hβ1 : 1 / 2 ≤ β) (hβ2 : β ≤ 1 - δ) :
    |liX (X ^ β)| ≤ 4 * Real.log X * Real.exp (-(δ * Real.log X)) * liX X := by
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log X := ⟨_, rfl⟩
  rw [← hL]
  have hXpos : 0 < X := by linarith
  have hL0 : 0 < L := by rw [hL]; exact Real.log_pos (by linarith)
  have hXL : X = Real.exp L := by rw [hL, Real.exp_log hXpos]
  have hXb2 : 2 ≤ X ^ β := by
    have h4 : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    calc (2 : ℝ) = 4 ^ ((1 : ℝ) / 2) := h4.symm
      _ ≤ X ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow (by norm_num) hX (by norm_num)
      _ ≤ X ^ β := Real.rpow_le_rpow_of_exponent_le (by linarith) hβ1
  obtain ⟨h0, hup⟩ := liX_upper hXb2
  have hlow : X / (2 * L) ≤ liX X := by rw [hL]; exact liX_lower hX
  calc |liX (X ^ β)| = liX (X ^ β) := abs_of_nonneg h0
    _ ≤ 2 * X ^ β := hup
    _ = 2 * Real.exp (β * L) := by rw [Real.rpow_def_of_pos hXpos, ← hL, mul_comm L β]
    _ ≤ 2 * Real.exp ((1 - δ) * L) := by
        have : β * L ≤ (1 - δ) * L := mul_le_mul_of_nonneg_right hβ2 hL0.le
        have := Real.exp_le_exp.2 this
        linarith
    _ = 4 * L * Real.exp (-(δ * L)) * (X / (2 * L)) := by
        rw [hXL, show (1 - δ) * L = -(δ * L) + L by ring, Real.exp_add]
        field_simp
        ring
    _ ≤ 4 * L * Real.exp (-(δ * L)) * liX X :=
        mul_le_mul_of_nonneg_left hlow (by positivity)


theorem eventually_log_cube (K a : ℝ) (hK : 0 < K) (ha : 0 < a) :
    ∃ x₂ : ℝ, ∀ x : ℝ, x₂ ≤ x → K * Real.log x ^ 3 ≤ x ^ a := by
  have h := (isLittleO_log_rpow_rpow_atTop 3 ha).bound (by positivity : (0 : ℝ) < 1 / K)
  obtain ⟨x₂, hx₂⟩ := Filter.eventually_atTop.1 (h.and (Filter.eventually_gt_atTop 0))
  refine ⟨x₂, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hx₂ x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos h2 a)] at h1
  have h3 : Real.log x ^ 3 = Real.log x ^ (3 : ℝ) := by
    rw [← Real.rpow_natCast]
    norm_num
  rw [h3]
  calc K * Real.log x ^ (3 : ℝ) ≤ K * |Real.log x ^ (3 : ℝ)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hK.le
    _ ≤ K * (1 / K * x ^ a) := mul_le_mul_of_nonneg_left h1 hK.le
    _ = x ^ a := by field_simp

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end
