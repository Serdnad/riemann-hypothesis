module

public import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
public import Formalism.GL3MeanSquares.Bundle001
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailMertens
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
public import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
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
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle006
public import Mathlib.NumberTheory.Primorial

@[expose] public section

section

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem oddM_odd (z : ℝ) (q : ℕ) (hq : q.Prime) (h2 : q ≠ 2) : Nat.Coprime 2 (oddM z q) := by
  have hq2 : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm h2)
  refine Nat.Coprime.mul_right hq2 (Nat.Coprime.prod_right fun p hp => ?_)
  have hp' := Finset.mem_filter.mp hp
  have h3 : 3 ≤ p := (Finset.mem_Icc.mp hp'.1).1
  exact (Nat.coprime_primes Nat.prime_two hp'.2).mpr (by omega)

private theorem chineseRemainder_finiteCover (M : ℕ) (h : Nat.Coprime 2 M) : ∃ a : ℕ, a.Coprime (16 * M) ∧
    ∀ d : ℕ, (d % 16 = 7 ∧ M ∣ d + 1) ↔ d % (16 * M) = a % (16 * M) := by
  have hM0 : M ≠ 0 := by
    rintro rfl
    simp at h
  have h16 : Nat.Coprime 16 M := by
    have := Nat.Coprime.pow_left 4 h
    norm_num at this
    exact this
  obtain ⟨c, hc1, hc2⟩ := Nat.chineseRemainder h16 7 (M - 1)
  have hc3 : c + 1 ≡ 0 [MOD M] := by
    have := hc2.add_right 1
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hM0)] at this
    exact this.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)
  have hc1' : c % 16 = 7 := hc1
  have key1 : ∀ d : ℕ, d % 16 = 7 ↔ d ≡ c [MOD 16] := by
    intro d
    unfold Nat.ModEq
    rw [hc1']
  have key2 : ∀ d : ℕ, M ∣ d + 1 ↔ d ≡ c [MOD M] := by
    intro d
    rw [← Nat.modEq_zero_iff_dvd]
    constructor
    · intro hd
      exact Nat.ModEq.add_right_cancel' 1 (hd.trans hc3.symm)
    · intro hd
      exact (hd.add_right 1).trans hc3
  have hcM : Nat.Coprime c M := by
    have hdvd : M ∣ c + 1 := Nat.modEq_zero_iff_dvd.mp hc3
    have hcc : Nat.Coprime c (c + 1) := by
      rw [Nat.coprime_self_add_right]
      exact Nat.coprime_one_right c
    exact Nat.Coprime.coprime_dvd_right hdvd hcc
  have hc16 : Nat.Coprime c 16 := by
    have := Nat.ModEq.gcd_eq hc1
    unfold Nat.Coprime
    rw [this]
    norm_num
  refine ⟨c, Nat.Coprime.mul_right hc16 hcM, fun d => ?_⟩
  rw [key1 d, key2 d]
  exact Nat.modEq_and_modEq_iff_modEq_mul h16

theorem exists_coprime_primePairSetSecond_eq_PPset :
    ∀ (z z' : ℝ) (q : ℕ), q.Prime → q ≠ 2 → ∃ a₀ : ℕ, a₀.Coprime (16 * oddM z q) ∧
      primeSetTwoBounds z z' q = PPset (16 * oddM z q) a₀ (Real.exp z') := by
  intro z z' q hq h2
  obtain ⟨a, ha, hiff⟩ := chineseRemainder_finiteCover _ (oddM_odd z q hq h2)
  refine ⟨a, ha, ?_⟩
  unfold primeSetTwoBounds PPset
  apply Finset.filter_congr
  intro d _
  rw [← hiff d]
  tauto

end QH
end

section

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

theorem rows_of_mem :
    ∀ (z z' : ℝ) (q d : ℕ), 0 < z → 2 * z ≤ z' → q ∈ primePairSetFirst z → d ∈ primeSetTwoBounds z z' q → Rows z z' q d := by
  intro z z' q d hz hzz hq hd
  have hhalf : ∀ t : ℝ, Real.exp t ^ (1 / 2 : ℝ) = Real.exp (t / 2) := by
    intro t
    rw [← Real.exp_mul]
    congr 1
    ring
  simp only [primePairSetFirst, PPset, primeSetTwoBounds, mem_filter, mem_Icc, hhalf] at hq hd
  obtain ⟨⟨_, hq2⟩, hqp, hqm, hqg⟩ := hq
  obtain ⟨⟨_, hd2⟩, hdp, hdm, hdv, hdg⟩ := hd
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hqp.pos
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hdp.pos
  have hqle : (q : ℝ) ≤ Real.exp z := (Nat.le_floor_iff (Real.exp_pos z).le).1 hq2
  have hdle : (d : ℝ) ≤ Real.exp z' := (Nat.le_floor_iff (Real.exp_pos z').le).1 hd2
  refine ⟨hqp, by omega, (Real.lt_log_iff_exp_lt hq0).2 hqg, (Real.log_le_iff_le_exp hq0).2 hqle,
    hdp, hdm, (Real.lt_log_iff_exp_lt hd0).2 hdg, (Real.log_le_iff_le_exp hd0).2 hdle, ?_, ?_⟩
  · have h1 : Real.exp z ≤ Real.exp (z' / 2) := Real.exp_le_exp.2 (by linarith)
    have h2 : (q : ℝ) < d := lt_of_le_of_lt (hqle.trans h1) hdg
    exact_mod_cast h2
  · intro p hp hp2 hpz
    apply Nat.mod_eq_zero_of_dvd
    refine Dvd.dvd.trans ?_ hdv
    unfold oddM
    rcases hpz with h | h
    · refine Dvd.dvd.mul_left ?_ _
      refine Finset.dvd_prod_of_mem (fun p : ℕ => p) ?_
      rw [mem_filter, mem_Icc]
      have h2 := hp.two_le
      exact ⟨⟨by omega, Nat.le_floor h⟩, hp⟩
    · rw [h]
      exact Dvd.intro _ rfl

end QH
end

section

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem real_split (M p : ℕ) (h : M.Coprime p) (χ : DirichletCharacter ℂ (M * p))
    (hχ : χ ^ 2 = 1) :
    ∃ (ξ : DirichletCharacter ℂ M) (η : DirichletCharacter ℂ p), ξ ^ 2 = 1 ∧ η ^ 2 = 1 ∧
      ∀ n : ℕ, n.Coprime (M * p) →
        χ (n : ZMod (M * p)) = ξ (n : ZMod M) * η (n : ZMod p) := by
  let E : (ZMod (M * p))ˣ ≃* (ZMod M)ˣ × (ZMod p)ˣ :=
    (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits
  let φ : (ZMod M)ˣ × (ZMod p)ˣ →* ℂˣ := χ.toUnitHom.comp E.symm.toMonoidHom
  have hφ : ∀ x, ((φ x : ℂˣ) : ℂ) ^ 2 = 1 := by
    intro x
    have h1 : ((φ x : ℂˣ) : ℂ) = χ ((E.symm x : (ZMod (M * p))ˣ) : ZMod (M * p)) := by
      simp [φ]
    rw [h1, ← MulChar.pow_apply_coe, hχ, MulChar.one_apply_coe]
  refine ⟨MulChar.ofUnitHom (φ.comp (MonoidHom.inl _ _)),
    MulChar.ofUnitHom (φ.comp (MonoidHom.inr _ _)), ?_, ?_, ?_⟩
  · ext u
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, MulChar.ofUnitHom_coe]
    exact hφ _
  · ext u
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, MulChar.ofUnitHom_coe]
    exact hφ _
  · intro n hn
    have hM : n.Coprime M := Nat.Coprime.coprime_mul_right_right hn
    have hp : n.Coprime p := Nat.Coprime.coprime_mul_left_right hn
    have hE : E (ZMod.unitOfCoprime n hn) = (ZMod.unitOfCoprime n hM, ZMod.unitOfCoprime n hp) := by
      have hc : (ZMod.chineseRemainder h) (n : ZMod (M * p)) = ((n : ZMod M), (n : ZMod p)) := by
        rw [map_natCast]; rfl
      refine Prod.ext (Units.ext ?_) (Units.ext ?_)
      · exact congrArg Prod.fst hc
      · exact congrArg Prod.snd hc
    rw [← ZMod.coe_unitOfCoprime n hn, ← ZMod.coe_unitOfCoprime n hM,
      ← ZMod.coe_unitOfCoprime n hp, MulChar.ofUnitHom_coe, MulChar.ofUnitHom_coe,
      ← Units.val_mul, MonoidHom.comp_apply φ, MonoidHom.comp_apply φ, ← map_mul]
    have : (MonoidHom.inl _ _ (ZMod.unitOfCoprime n hM) * MonoidHom.inr _ _ (ZMod.unitOfCoprime n hp)
        : (ZMod M)ˣ × (ZMod p)ˣ) = E (ZMod.unitOfCoprime n hn) := by
      rw [hE]; simp
    rw [this]
    simp [φ]

private theorem real_prime (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (η : DirichletCharacter ℂ p)
    (hη : η ^ 2 = 1) :
    ∃ a : ℕ, a ≤ 1 ∧ ∀ n : ℕ, n.Coprime p → η (n : ZMod p) = J p n ^ a := by
  haveI := Fact.mk hp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have key : ∀ θ : MulChar (ZMod p) ℂ, θ ^ 2 = 1 → θ ≠ 1 → θ g = -1 := by
    intro θ h1 hne
    have h3 : θ g ^ 2 = 1 := by rw [← MulChar.pow_apply_coe, h1, MulChar.one_apply_coe]
    rcases mul_self_eq_one_iff.mp (by rw [← sq]; exact h3 : θ g * θ g = 1) with h | h
    · exfalso
      apply hne
      rw [MulChar.eq_iff hg, h, MulChar.one_apply_coe]
    · exact h
  by_cases h1 : η = 1
  · refine ⟨0, by norm_num, fun n hn => ?_⟩
    rw [h1, pow_zero, ← ZMod.coe_unitOfCoprime n hn, MulChar.one_apply_coe]
  · refine ⟨1, le_rfl, fun n _ => ?_⟩
    let ψ : MulChar (ZMod p) ℂ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
    have hψ1 : ψ ≠ 1 := by
      refine (MulChar.ringHomComp_ne_one_iff (RingHom.injective_int _)).mpr ?_
      exact quadraticChar_ne_one (by rw [ZMod.ringChar_zmod_n]; exact h2)
    have hψ2 : ψ ^ 2 = 1 :=
      ((quadraticChar_isQuadratic (ZMod p)).comp _).sq_eq_one
    have he : η = ψ := by
      rw [MulChar.eq_iff hg, key η hη h1, key ψ hψ2 hψ1]
    rw [he, pow_one, J, ← jacobiSym.legendreSym.to_jacobiSym]
    simp [ψ, legendreSym]

private theorem real_one_step (M p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (hM : ¬ p ∣ M)
    (χ : DirichletCharacter ℂ (M * p)) (hχ : χ ^ 2 = 1) :
    ∃ (ξ : DirichletCharacter ℂ M) (a : ℕ), ξ ^ 2 = 1 ∧ a ≤ 1 ∧
      ∀ n : ℕ, n.Coprime (M * p) → χ (n : ZMod (M * p)) = ξ (n : ZMod M) * J p n ^ a := by
  obtain ⟨ξ, η, h1, h3, h4⟩ :=
    real_split M p ((Nat.Prime.coprime_iff_not_dvd hp).mpr hM).symm χ hχ
  obtain ⟨a, ha, h5⟩ := real_prime p hp h2 η h3
  exact ⟨ξ, a, h1, ha, fun n hn => by
    rw [h4 n hn, h5 n (Nat.Coprime.coprime_mul_left_right hn)]⟩

theorem real_decomp :
    ∀ (N₀ q d : ℕ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ^ 2 = 1 → 0 < N₀ → q.Prime → d.Prime → q ≠ 2 → d ≠ 2 → q ≠ d → ¬ q ∣ N₀ → ¬ d ∣ N₀ →
      N ∣ N₀ * q * d → ∃ (ξ : DirichletCharacter ℂ N₀) (a b : ℕ), a ≤ 1 ∧ b ≤ 1 ∧
        ∀ n : ℕ, n.Coprime (N₀ * q * d) → χ (n : ZMod N) = ξ (n : ZMod N₀) * J q n ^ a * J d n ^ b := by
  intro N₀ q d N _ χ hχ _ hq hd hq2 hd2 hqd hqN hdN hN
  have hdq : ¬ d ∣ N₀ * q := by
    intro h
    rcases (Nat.Prime.dvd_mul hd).mp h with h | h
    · exact hdN h
    · exact hqd ((Nat.prime_dvd_prime_iff_eq hd hq).mp h).symm
  have hχ' : (DirichletCharacter.changeLevel hN χ) ^ 2 = 1 := by
    rw [← map_pow, hχ, map_one]
  obtain ⟨ξ₁, b, h1, hb, h3⟩ := real_one_step (N₀ * q) d hd hd2 hdq _ hχ'
  obtain ⟨ξ, a, _, ha, h4⟩ := real_one_step N₀ q hq hq2 hqN ξ₁ h1
  refine ⟨ξ, a, b, ha, hb, fun n hn => ?_⟩
  rw [← h4 n (Nat.Coprime.coprime_mul_right_right hn), ← h3 n hn,
    ← ZMod.coe_unitOfCoprime n hn, DirichletCharacter.changeLevel_eq_cast_of_dvd,
    ZMod.coe_unitOfCoprime, ZMod.cast_natCast hN]

end QH
end

section

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem noExc_mono {c c' : ℝ} (h : c' ≤ c) {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hc : NoExc c χ) : NoExc c' χ :=
  fun β h1 h2 => hc β (by linarith) h2

private theorem noExc_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ∃ c : ℝ, 0 < c ∧ (χ ≠ 1 → NoExc c χ) := by
  by_cases hχ : χ = 1
  · exact ⟨1, one_pos, fun h => absurd hχ h⟩
  have hcont : Continuous (fun β : ℝ => DirichletCharacter.LFunction χ (β : ℂ)) :=
    (DirichletCharacter.differentiable_LFunction hχ).continuous.comp Complex.continuous_ofReal
  have h1 : (fun β : ℝ => DirichletCharacter.LFunction χ (β : ℂ)) 1 ≠ 0 := by
    simpa using DirichletCharacter.LFunction_apply_one_ne_zero hχ
  have hev := hcont.continuousAt.eventually_ne h1
  obtain ⟨c, hc, h⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨c, hc, fun _ β hb1 hb2 => h ?_⟩
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

private theorem noExc_level (N : ℕ) [NeZero N] :
    ∃ c : ℝ, 0 < c ∧ ∀ χ : DirichletCharacter ℂ N, χ ≠ 1 → NoExc c χ := by
  classical
  choose c hc h using fun χ : DirichletCharacter ℂ N => noExc_one χ
  obtain ⟨χ₀, hχ₀⟩ := Finite.exists_min c
  exact ⟨c χ₀, hc χ₀, fun χ hχ => noExc_mono (hχ₀ χ) (h χ hχ)⟩

theorem small_zeros :
    ∀ N₀ : ℕ, ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), N ≤ N₀ → χ ≠ 1 → NoExc c₀ χ := by
  intro N₀
  induction N₀ with
  | zero =>
    exact ⟨1, one_pos, fun N _ χ hN _ => absurd (Nat.le_zero.1 hN) (NeZero.ne N)⟩
  | succ n ih =>
    obtain ⟨c, hc, h⟩ := ih
    obtain ⟨c', hc', h'⟩ := noExc_level (n + 1)
    refine ⟨min c c', lt_min hc hc', fun N _ χ hN hχ => ?_⟩
    rcases Nat.lt_or_eq_of_le hN with hlt | heq
    · exact noExc_mono (min_le_left _ _) (h N χ (Nat.lt_succ_iff.1 hlt) hχ)
    · subst heq
      exact noExc_mono (min_le_right _ _) (h' χ hχ)

end QH
end

section

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

theorem log_oddM :
    ∀ (z : ℝ) (q : ℕ), 0 ≤ z → 0 < q → Real.log ((16 * oddM z q : ℕ) : ℝ) ≤ Real.log 16 + Real.log q + z * Real.log 4 := by
  intro z q hz hq
  have hPle : (∏ p ∈ Icc 3 ⌊z⌋₊ with Nat.Prime p, p) ≤ 4 ^ ⌊z⌋₊ := by
    refine le_trans ?_ (primorial_le_four_pow ⌊z⌋₊)
    unfold primorial
    apply Finset.prod_le_prod_of_subset_of_one_le'
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hp ⊢
      exact ⟨by omega, hp.2⟩
    · intro p hp _
      simp only [Finset.mem_filter] at hp
      exact hp.2.one_lt.le
  have hPpos : 0 < (∏ p ∈ Icc 3 ⌊z⌋₊ with Nat.Prime p, p) :=
    Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.pos)
  have hoddM : oddM z q = q * (∏ p ∈ Icc 3 ⌊z⌋₊ with Nat.Prime p, p) := rfl
  generalize (∏ p ∈ Icc 3 ⌊z⌋₊ with Nat.Prime p, p) = P at hPle hPpos hoddM
  rw [hoddM]
  have hPR : (0 : ℝ) < P := by exact_mod_cast hPpos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hPle' : (P : ℝ) ≤ 4 ^ ⌊z⌋₊ := by exact_mod_cast hPle
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  have h1 : Real.log P ≤ (⌊z⌋₊ : ℝ) * Real.log 4 := by
    calc Real.log P ≤ Real.log ((4 : ℝ) ^ ⌊z⌋₊) := Real.log_le_log hPR hPle'
      _ = (⌊z⌋₊ : ℝ) * Real.log 4 := by rw [Real.log_pow]
  have h2 : (⌊z⌋₊ : ℝ) ≤ z := Nat.floor_le hz
  have h3 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  nlinarith

end QH
end

section

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

theorem sum_cN_le :
    ∃ C : ℝ, 0 < C ∧ ∀ y Z : ℝ, 0 ≤ y → 2 ≤ Z → ∑ n ∈ Icc 1 ⌊Z⌋₊, cN y n ≤ C * y * Real.log Z := by
  obtain ⟨C, hC, hM⟩ := Formalism.HermitianLattices.Ext.BoxTail.tail_mertens
  refine ⟨C + 1, by linarith, fun y Z hy hZ => ?_⟩
  have hlog : 0 ≤ Real.log Z := Real.log_nonneg (by linarith)
  calc ∑ n ∈ Icc 1 ⌊Z⌋₊, cN y n
        ≤ ∑ n ∈ Icc 1 ⌊Z⌋₊, y * (ArithmeticFunction.vonMangoldt n / (n : ℝ)) := by
          apply Finset.sum_le_sum
          intro n hn
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
          have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
          simp only [cN]
          calc ArithmeticFunction.vonMangoldt n * min 1 (y / n)
              ≤ ArithmeticFunction.vonMangoldt n * (y / n) :=
                mul_le_mul_of_nonneg_left (min_le_right _ _) hΛ
            _ = y * (ArithmeticFunction.vonMangoldt n / n) := by ring
    _ = y * ∑ n ∈ Icc 1 ⌊Z⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
          rw [Finset.mul_sum]
    _ ≤ y * (C * Real.log Z) := mul_le_mul_of_nonneg_left (hM Z hZ) hy
    _ ≤ (C + 1) * y * Real.log Z := by nlinarith [mul_nonneg hy hlog]

end QH
end
