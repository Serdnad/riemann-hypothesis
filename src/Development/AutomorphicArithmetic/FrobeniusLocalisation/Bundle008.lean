module

public import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs
public import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle002
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle295
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle004
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle005
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle006
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle007
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Ideal.Int
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem half_le_vd {φ : Frame} (H : HostAx φ) {l : ℕ} (hl : l.Prime) :
    (H.condE.factorization l : ℝ) ≤ 2 * H.vdH l := by
  have heN := (layer_bot H.toHostRaw hl (Nat.zero_le (H.condN.factorization l))).2.2
  rw [vd_formula H hl]
  have hnn : ∀ c : ℕ, (0 : ℝ) ≤ 1 - 1 / (c : ℝ) := by
    intro c
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp
    · have h1 : (1 : ℝ) / c ≤ 1 := by
        rw [div_le_one (by exact_mod_cast hc)]
        exact_mod_cast hc
      linarith
  have hhalf : ∀ c : ℕ, c ≠ 1 → (1 : ℝ) / 2 ≤ 1 - 1 / (c : ℝ) := by
    intro c hc
    rcases c with _ | _ | c
    · norm_num
    · exact absurd rfl hc
    · have h1 : (1 : ℝ) / ((c + 1 + 1 : ℕ) : ℝ) ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) (by push_cast; linarith [(Nat.cast_nonneg c : (0 : ℝ) ≤ c)])
      linarith
  calc (H.condE.factorization l : ℝ)
      = 2 * ∑ j ∈ Finset.range (H.condE.factorization l), (1 / 2 : ℝ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
    _ ≤ 2 * ∑ j ∈ Finset.range (H.condE.factorization l),
        (1 - 1 / (Nat.card (UpperTheory.HF.Formalism.HC.HostRaw.imgOne H.toHostRaw
          (H.condN / l ^ H.condN.factorization l * l ^ j)) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum
        intro j hj
        apply hhalf
        rw [Ne, Subgroup.card_eq_one]
        have hjN : j ≤ H.condN.factorization l := (Finset.mem_range.1 hj).le.trans heN
        rw [(layer_bot H.toHostRaw hl hjN).1]
        exact not_le.2 (Finset.mem_range.1 hj)
    _ ≤ 2 * ∑ j ∈ Finset.range (H.condN.factorization l),
        (1 - 1 / (Nat.card (UpperTheory.HF.Formalism.HC.HostRaw.imgOne H.toHostRaw
          (H.condN / l ^ H.condN.factorization l * l ^ j)) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 heN)
          (fun j _ _ => hnn _)

theorem UpperTheory.HF.cond_rd :
    ∀ {φ : Frame} (H : HostAx φ), H.rd ≤ H.condE ∧ Real.log H.rd ≤ Real.log H.condE ∧ Real.log H.condE ≤ Real.log H.condN ∧ (H.condE : ℝ) ≤ H.rd ^ 2 ∧ 4 * φ.ord ≤ H.condE.totient ∧ 4 * φ.ord ∣ H.condE.totient ∧ 4 * φ.ord ≤ H.condE := by
  intro φ H
  obtain ⟨hEN, hE0, hspec⟩ := condE_spec H.toHostRaw
  have hN0 := H.condN_ne_zero
  obtain ⟨-, hlogrd, -, hrd0⟩ := log_rd_sum H
  have hE0' : (0 : ℝ) < H.condE := by exact_mod_cast hE0
  have logE : Real.log H.condE =
      ∑ l ∈ H.condN.primeFactors, (H.condE.factorization l : ℝ) * Real.log l := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
    apply Finset.sum_subset (Nat.primeFactors_mono hEN hN0)
    intro l _ hl
    have h0 : H.condE.factorization l = 0 := by
      rwa [← Nat.support_factorization, Finsupp.mem_support_iff, not_not] at hl
    simp [h0]
  have hb : Real.log H.rd ≤ Real.log H.condE := by
    rw [hlogrd, logE]
    apply Finset.sum_le_sum
    intro l hl
    have hlp := Nat.prime_of_mem_primeFactors hl
    exact mul_le_mul_of_nonneg_right (vd_le H hlp).2
      (Real.log_nonneg (by exact_mod_cast hlp.one_lt.le))
  have hd : Real.log H.condE ≤ 2 * Real.log H.rd := by
    rw [hlogrd, logE, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l hl
    have hlp := Nat.prime_of_mem_primeFactors hl
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (half_le_vd H hlp)
      (Real.log_nonneg (by exact_mod_cast hlp.one_lt.le))
  have ha : H.rd ≤ H.condE := (Real.log_le_log_iff hrd0 hE0').1 hb
  have hcE : (H.condE : ℝ) ≤ H.rd ^ 2 := by
    rw [← Real.log_le_log_iff hE0' (by positivity), Real.log_pow]
    push_cast
    linarith
  have hc : Real.log H.condE ≤ Real.log H.condN :=
    Real.log_le_log hE0' (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hEN)
  have htop : UpperTheory.HF.Formalism.HC.HostRaw.imgOne H.toHostRaw 1 = ⊤ := by
    ext g
    simp only [Subgroup.mem_top, iff_true]
    obtain ⟨u, rfl⟩ := H.der.art_surj g
    exact (UpperTheory.HF.Formalism.HC.HostRaw.mem_imgOne H.toHostRaw (one_dvd _) _).2 ⟨u, Nat.modEq_one, rfl⟩
  have hbot : UpperTheory.HF.Formalism.HC.HostRaw.imgOne H.toHostRaw H.condE = ⊥ := (hspec _ hEN).2 dvd_rfl
  have hdvd := card_imgOne_dvd H.toHostRaw (one_dvd H.condE) hEN
  rw [htop, hbot, Subgroup.card_top, Subgroup.card_bot, Nat.totient_one, Nat.div_one, one_mul,
    (φ.hostGroup).1] at hdvd
  have htpos : 0 < H.condE.totient := Nat.totient_pos.2 hE0
  exact ⟨ha, hb, hc, hcE, Nat.le_of_dvd htpos hdvd, hdvd,
    (Nat.le_of_dvd htpos hdvd).trans (Nat.totient_le _)⟩
end

section

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.rad_bounds :
    ∀ {φ : Frame} (H : HostAx φ), Real.log H.rad ≤ 2 * Real.log H.rd ∧ (H.ram.card : ℝ) ≤ 2 * Real.log H.rd / Real.log 2 ∧ (∀ D₀ : ℝ, 0 ≤ D₀ → ∑ l ∈ H.ram, (⌈H.vdH l * D₀⌉ : ℝ) * Real.log l ≤ (D₀ + 2) * Real.log H.rd) ∧ ((∏ l ∈ H.ram, l ^ ⌈H.vdH l⌉₊ : ℕ) : ℝ) ≤ H.rd ^ 2 ∧ ∀ g₁ g₂ L : ℝ, 0 < g₁ → 0 < g₂ → Real.log g₁ ≤ 9 * L + 1 → Real.log g₂ ≤ 9 * L + 1 → Real.log H.rd ≤ L / 100 → Real.log (g₁ * g₂ * H.rad) ≤ Real.log (g₁ * g₂) + 2 * Real.log H.rd ∧ Real.log (g₁ * g₂) + 2 * Real.log H.rd ≤ 18 * L + 2 + L / 50 := by
  intro φ H
  obtain ⟨hs, -, -, hrd⟩ := UpperTheory.HF.log_rd_sum H
  have hp : ∀ l ∈ H.ram, l.Prime := fun l hl => Nat.prime_of_mem_primeFactors hl
  have hv : ∀ l ∈ H.ram, 1 / 2 ≤ H.vdH l := fun l hl => (UpperTheory.HF.mem_ram H (hp l hl)).2.2.2.1 hl
  have hl0 : ∀ l ∈ H.ram, (0 : ℝ) < l := fun l hl => Nat.cast_pos.2 (hp l hl).pos
  have hlog2 : ∀ l ∈ H.ram, Real.log 2 ≤ Real.log l := fun l hl =>
    Real.log_le_log (by norm_num) (by exact_mod_cast (hp l hl).two_le)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : ∀ l ∈ H.ram, 0 ≤ Real.log l := fun l hl => h2.le.trans (hlog2 l hl)
  have hsum : ∑ l ∈ H.ram, Real.log l ≤ 2 * Real.log H.rd := by
    rw [hs, Finset.mul_sum]
    refine Finset.sum_le_sum fun l hl => ?_
    nlinarith [hv l hl, hlog l hl]
  have hradpos : (0 : ℝ) < H.rad := by
    unfold HostRaw.rad
    rw [Nat.cast_prod]
    exact Finset.prod_pos hl0
  have h1 : Real.log H.rad ≤ 2 * Real.log H.rd := by
    refine le_trans (le_of_eq ?_) hsum
    unfold HostRaw.rad
    rw [Nat.cast_prod, Real.log_prod fun l hl => (hl0 l hl).ne']
  refine ⟨h1, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ h2]
    refine le_trans ?_ hsum
    have := Finset.card_nsmul_le_sum H.ram (fun l : ℕ => Real.log l) _ hlog2
    simpa using this
  · intro D₀ hD
    rw [hs, Finset.mul_sum]
    refine Finset.sum_le_sum fun l hl => ?_
    have hc : (⌈H.vdH l * D₀⌉ : ℝ) ≤ (D₀ + 2) * H.vdH l := by
      have := (Int.ceil_lt_add_one (H.vdH l * D₀)).le
      nlinarith [hv l hl]
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hc (hlog l hl)
  · have hpos : (0 : ℝ) < ((∏ l ∈ H.ram, l ^ ⌈H.vdH l⌉₊ : ℕ) : ℝ) := by
      rw [Nat.cast_prod]
      exact Finset.prod_pos fun l hl => by
        rw [Nat.cast_pow]; exact pow_pos (hl0 l hl) _
    rw [← Real.log_le_log_iff hpos (pow_pos hrd 2), Real.log_pow, Nat.cast_prod,
      Real.log_prod fun l hl => by rw [Nat.cast_pow]; exact (pow_pos (hl0 l hl) _).ne', hs, Finset.mul_sum]
    refine Finset.sum_le_sum fun l hl => ?_
    rw [Nat.cast_pow, Real.log_pow, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (hlog l hl)
    have hy := hv l hl
    push_cast
    by_cases h : H.vdH l ≤ 1
    · have : ⌈H.vdH l⌉₊ ≤ 1 := Nat.ceil_le.2 (by simpa using h)
      have : (⌈H.vdH l⌉₊ : ℝ) ≤ 1 := by exact_mod_cast this
      linarith
    · have := (Nat.ceil_lt_add_one (by linarith : 0 ≤ H.vdH l)).le
      push Not at h
      linarith
  · intro g₁ g₂ L h₁ h₂ hg₁ hg₂ hL
    constructor
    · rw [Real.log_mul (mul_pos h₁ h₂).ne' hradpos.ne']
      linarith
    · rw [Real.log_mul h₁.ne' h₂.ne']
      linarith
end

section

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.inert_d :
    ∀ {φ : Frame} (H : HostAx φ), H.inertG H.d = Subgroup.zpowers φ.iod ∧ H.el H.d = 2 ∧ H.vdH H.d = 1 / 2 ∧ H.sl H.d = 1 ∧ H.d ∈ H.ram ∧ 2 ∈ H.ram ∧ H.condE.factorization H.d = 1 := by
  intro φ H
  haveI : Fact (Nat.Prime H.d) := ⟨H.d_prime⟩
  have hd := H.d_prime
  have hQq : H.QS * H.q ≠ 0 := Nat.mul_ne_zero H.QS_ne_zero H.q_prime.ne_zero
  have hfac : H.condN.factorization H.d = 1 := by
    show (H.QS * H.q * H.d).factorization H.d = 1
    rw [Nat.factorization_mul hQq hd.ne_zero, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd H.d_not_dvd_QSq, hd.factorization_self]
  have hquot : H.condN / H.d ^ H.condN.factorization H.d = H.QS * H.q := by
    rw [hfac, pow_one]
    exact Nat.mul_div_cancel _ hd.pos
  have hmem : φ.iod ∈ H.inertG H.d := by
    obtain ⟨P, hPm, hPl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 H.E)
      (Ideal.span {(H.d : ℤ)})
    have h1 := (H.der.inertia_d P (H.gal.symm φ.iod)).2 (Or.inr (by simp))
    obtain ⟨u, hu, h⟩ := (H.der.inertia H.d P (H.gal.symm φ.iod)).1 h1
    exact (H.mem_inertG H.d _).2 ⟨u, hu, by simpa using h⟩
  have hG : H.inertG H.d = Subgroup.zpowers φ.iod := by
    refine le_antisymm (fun g hg => ?_) (Subgroup.zpowers_le.2 hmem)
    obtain ⟨u, hu, rfl⟩ := (H.mem_inertG H.d g).1 hg
    rw [hquot] at hu
    rcases H.art_d u hu with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact Subgroup.mem_zpowers _
  have hord : orderOf φ.iod = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by simp [Frame.iod, sq, Prod.ext_iff]) (by simp [Frame.iod, Prod.ext_iff])
  have hel : H.el H.d = 2 := by
    show Nat.card (H.inertG H.d) = 2
    rw [hG, Nat.card_zpowers, hord]
  have hndvd : ¬ H.d ∣ H.el H.d := by
    rw [hel]
    exact (Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).not.2 H.d_ne_two
  have htw := vd_tame_wild H hd
  have hv : H.vdH H.d = 1 / 2 := by
    rw [htw.1 hndvd, hel]
    norm_num
  have hs : H.sl H.d = 1 := htw.2.2 hndvd
  have hram := mem_ram H hd
  have hdram : H.d ∈ H.ram := hram.1.2 (by rw [hel]; norm_num)
  have h2ram : 2 ∈ H.ram := by
    show 2 ∈ (NumberField.discr H.E).natAbs.primeFactors
    refine Nat.mem_primeFactors.2 ⟨Nat.prime_two, ?_, Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero H.E)⟩
    exact Int.natAbs_dvd_natAbs.2 (H.der.discr_primes).2.1
  have hpos := (condE_spec H.toHostRaw).2.1
  have hdvd : H.d ∣ H.condE := hram.2.1.1 hdram
  have hle : H.condE.factorization H.d ≤ 1 := by
    have h : max 1 (H.condE.factorization H.d) = 1 := hs
    exact max_eq_left_iff.1 h
  have hge : 1 ≤ H.condE.factorization H.d := (hd.dvd_iff_one_le_factorization hpos.ne').1 hdvd
  exact ⟨hG, hel, hv, hs, hdram, h2ram, le_antisymm hle hge⟩
end

section

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem ordCompl_q {φ : Frame} (H : HostRaw φ) : ordCompl[H.q] H.condN = H.QS * H.d := by
  have hq := H.q_prime
  have hQd : H.QS * H.d ≠ 0 := Nat.mul_ne_zero H.QS_ne_zero H.d_prime.ne_zero
  have hnd : ¬ H.q ∣ H.QS * H.d := fun h =>
    hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm H.coprime_QSd_q) h)
  have hN : H.condN = H.QS * H.d * H.q := by
    show H.QS * H.q * H.d = H.QS * H.d * H.q
    ring
  have hfac : H.condN.factorization H.q = 1 := by
    rw [hN, Nat.factorization_mul hQd hq.ne_zero, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnd, hq.factorization_self]
  rw [hfac, pow_one, hN]
  exact Nat.mul_div_cancel _ hq.pos

private theorem QSd_dvd {φ : Frame} (H : HostRaw φ) : H.QS * H.d ∣ H.condN :=
  ⟨H.q, by unfold HostRaw.condN; ring⟩

private theorem cyc_unitsOne {φ : Frame} (H : HostRaw φ) : IsCyclic (H.unitsOne (H.QS * H.d)) := by
  haveI : Fact (Nat.Prime H.q) := ⟨H.q_prime⟩
  have hN : H.condN = H.QS * H.d * H.q := by
    show H.QS * H.q * H.d = H.QS * H.d * H.q
    ring
  haveI : NeZero H.condN := ⟨by
    rw [hN]
    exact Nat.mul_ne_zero (Nat.mul_ne_zero H.QS_ne_zero H.d_prime.ne_zero) H.q_prime.ne_zero⟩
  let f : H.unitsOne (H.QS * H.d) →* ZMod H.q :=
    (Units.coeHom (ZMod H.q)).comp ((ZMod.unitsMap H.q_dvd_condN).comp (Subgroup.subtype _))
  refine isCyclic_of_injective_ringHom f ?_
  intro a b hab
  have ha := (H.mem_unitsOne (QSd_dvd H) a).1 a.2
  have hb := (H.mem_unitsOne (QSd_dvd H) b).1 b.2
  have hq : ((a : (ZMod H.condN)ˣ) : ZMod H.condN).val ≡ ((b : (ZMod H.condN)ˣ) : ZMod H.condN).val [MOD H.q] := by
    simp only [f, MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply, Subgroup.coe_subtype,
      ZMod.unitsMap_val] at hab
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, ZMod.natCast_val]
    exact hab
  have hm := (Nat.modEq_and_modEq_iff_modEq_mul H.coprime_QSd_q).1 ⟨ha.trans hb.symm, hq⟩
  rw [← hN] at hm
  have := Nat.ModEq.eq_of_lt_of_lt hm (ZMod.val_lt _) (ZMod.val_lt _)
  exact Subtype.ext (Units.ext (ZMod.val_injective _ this))

private theorem el_q_dvd {φ : Frame} (H : HostRaw φ) : H.el H.q ∣ 2 := by
  show Nat.card (H.inertG H.q) ∣ 2
  show Nat.card (H.imgOne (H.condN / H.q ^ H.condN.factorization H.q)) ∣ 2
  rw [ordCompl_q H]
  show Nat.card (Subgroup.map H.art (H.unitsOne (H.QS * H.d))) ∣ 2
  haveI := cyc_unitsOne H
  haveI : IsCyclic (Subgroup.map H.art (H.unitsOne (H.QS * H.d))) :=
    isCyclic_of_surjective (H.art.subgroupMap _) (H.art.subgroupMap_surjective _)
  rw [← IsCyclic.exponent_eq_card]
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  rintro ⟨g, hg⟩
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hg
  apply Subtype.ext
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
  exact H.art_q u ((H.mem_unitsOne (QSd_dvd H) u).1 hu)

private theorem el_q_ne_one {φ : Frame} (H : HostRaw φ) (h : H.PsQ) : H.el H.q ≠ 1 := by
  intro h1
  have hq := H.q_prime
  have hbot : H.inertG H.q = ⊥ := Subgroup.card_eq_one.1 h1
  obtain ⟨p, hp1, hp2⟩ := Nat.chineseRemainder H.coprime_QSd_q 1 (H.q - 1)
  have hN : H.condN = H.QS * H.d * H.q := by
    show H.QS * H.q * H.d = H.QS * H.d * H.q
    ring
  have hcq : Nat.Coprime p H.q := by
    rw [Nat.Coprime, Nat.ModEq.gcd_eq hp2, Nat.gcd_comm, ← Nat.Coprime, hq.coprime_iff_not_dvd]
    exact Nat.not_dvd_of_pos_of_lt (by have := hq.two_le; omega) (by have := hq.two_le; omega)
  have hcQd : Nat.Coprime p (H.QS * H.d) := by
    rw [Nat.Coprime, Nat.ModEq.gcd_eq hp1, Nat.gcd_one_left]
  have hcop : Nat.Coprime p H.condN := by
    rw [hN]
    exact Nat.Coprime.mul_right hcQd hcq
  set u := ZMod.unitOfCoprime p hcop
  have hu : (u : ZMod H.condN).val ≡ p [MOD H.condN] := H.val_unitOfCoprime hcop
  have hmem : H.art u ∈ H.inertG H.q := by
    refine (H.mem_inertG H.q _).2 ⟨u, ?_, rfl⟩
    rw [ordCompl_q H]
    exact (hu.of_dvd (QSd_dvd H)).trans hp1
  rw [hbot, Subgroup.mem_bot] at hmem
  have hJ := h u
  rw [hmem, jacobi_congr ((hu.of_dvd H.q_dvd_condN).trans hp2)] at hJ
  have hc : ((H.q - 1 : ℕ) : ℤ) = -1 + (H.q : ℤ) * 1 := by
    push_cast [Nat.cast_sub hq.one_le]
    ring
  rw [hc, jacobiSym.mod_left, Int.add_mul_emod_self_left, ← jacobiSym.mod_left,
    jacobiSym.at_neg_one (hq.odd_of_ne_two H.q_ne_two), ZMod.χ₄_nat_three_mod_four H.q_mod_four] at hJ
  simp at hJ

theorem UpperTheory.HF.inert_q :
    ∀ {φ : Frame} (H : HostAx φ), H.el H.q ≤ 2 ∧ H.sl H.q = 1 ∧ (H.q ∈ H.ram → H.el H.q = 2 ∧ H.vdH H.q = 1 / 2 ∧ H.condE.factorization H.q = 1) ∧ (H.q ∉ H.ram → H.vdH H.q = 0) ∧ (H.PsQ → H.q ∈ H.ram) := by
  intro φ H
  have hq := H.q_prime
  have h2 := el_q_dvd H.toHostRaw
  have hndvd : ¬ H.q ∣ H.el H.q := fun h =>
    H.q_ne_two ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (h.trans h2))
  have htw := vd_tame_wild H hq
  have hram := mem_ram H hq
  have hs : H.sl H.q = 1 := htw.2.2 hndvd
  refine ⟨Nat.le_of_dvd two_pos h2, hs, fun hmem => ?_, fun hmem => ?_, fun hP => ?_⟩
  · have hel : H.el H.q = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
      · exact absurd h (hram.1.1 hmem)
      · exact h
    refine ⟨hel, ?_, ?_⟩
    · rw [htw.1 hndvd, hel]
      norm_num
    · have hpos := (condE_spec H.toHostRaw).2.1
      have hdvd : H.q ∣ H.condE := hram.2.1.1 hmem
      have hle : H.condE.factorization H.q ≤ 1 := by
        have h : max 1 (H.condE.factorization H.q) = 1 := hs
        exact max_eq_left_iff.1 h
      exact le_antisymm hle ((hq.dvd_iff_one_le_factorization hpos.ne').1 hdvd)
  · by_contra h
    exact hmem (hram.2.2.1.2 h)
  · exact hram.1.2 (el_q_ne_one H.toHostRaw hP)
end

section

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.diff_mult :
    ∀ {φ : Frame} (H : HostAx φ) {l : ℕ}, l.Prime → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})], (multiplicity P (differentIdeal ℤ (𝓞 H.E)) : ℝ) = H.el l * H.vdH l ∧ multiplicity P (span {(l : 𝓞 H.E)}) = H.el l ∧ (¬ l ∣ H.el l → multiplicity P (differentIdeal ℤ (𝓞 H.E)) = H.el l - 1) ∧ (l ∣ H.el l → H.el l ≤ multiplicity P (differentIdeal ℤ (𝓞 H.E))) := by
  intro φ H l hl P _ _
  haveI := H.galois
  obtain ⟨-, -, hram, -⟩ := grp_bridge H hl P
  have hmap : (span {(l : ℤ)}).map (algebraMap ℤ (𝓞 H.E)) = span {(l : 𝓞 H.E)} := by
    simp [Ideal.map_span]
  have hne : (span {(l : ℤ)}).map (algebraMap ℤ (𝓞 H.E)) ≠ ⊥ :=
    map_ne_bot_of_ne_bot (by simp [hl.ne_zero])
  have hmult : multiplicity P (span {(l : 𝓞 H.E)}) = H.el l := by
    rw [← hmap, ← IsDedekindDomain.ramificationIdx_eq_multiplicity _ _ hne, hram]
  have hmem : (l : 𝓞 H.E) ∈ P := by
    have hle : span {(l : 𝓞 H.E)} ≤ P := by
      rw [← hmap]
      exact map_le_of_le_comap (Ideal.LiesOver.over (P := P) (p := span {(l : ℤ)})).le
    exact hle (Ideal.mem_span_singleton_self _)
  have hrat := GlobalTheory.DifferentElement.mult_ratio H.E l hl P inferInstance hmem
  rw [hmult, Nat.factorization_def _ hl] at hrat
  have hel0 : (0 : ℝ) < H.el l := by exact_mod_cast HostRaw.el_pos _ l
  have hvd : H.vdH l = (multiplicity P (differentIdeal ℤ (𝓞 H.E)) : ℝ) / H.el l := by
    have hr := congrArg (fun q : ℚ => (q : ℝ)) hrat
    push_cast at hr
    simp only [HostRaw.vdH, Nat.padicValNat_def]
    exact hr.symm
  have h1 : (multiplicity P (differentIdeal ℤ (𝓞 H.E)) : ℝ) = H.el l * H.vdH l := by
    rw [hvd]
    field_simp
  obtain ⟨htw1, htw2, -⟩ := vd_tame_wild H hl
  refine ⟨h1, hmult, fun hnd => ?_, fun hd => ?_⟩
  · have hv := htw1 hnd
    have hle : 1 ≤ H.el l := HostRaw.el_pos _ l
    have h2 : (multiplicity P (differentIdeal ℤ (𝓞 H.E)) : ℝ) = ((H.el l - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hle, h1, hv]
      field_simp
      push_cast
      ring
    exact_mod_cast h2
  · have hv := htw2 hd
    have h2 : (H.el l : ℝ) ≤ multiplicity P (differentIdeal ℤ (𝓞 H.E)) := by
      rw [h1]
      nlinarith
    exact_mod_cast h2
end
