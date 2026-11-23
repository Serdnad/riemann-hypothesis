module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle212
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle225
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle226
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle228
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCmIdempotentsSelectConjugatePrimes
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle227
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle222
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

namespace GlobalTheory.GalTheta

theorem adapted_lift_deeper : ∀ (D : D7), galStar D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ, FixK D ⊤ σ → ∀ (c c' : ℂ) (n₀ n : ℕ), 0 < n₀ → 0 < n → InRationalLattice (lamOf D cc δ) c → Adp1 ⊤ σ (lamOf D cc δ) n₀ c c' → ∃ ω ∈ lamOf D cc δ, Adp1 ⊤ σ (lamOf D cc δ) (n₀ * n) (c + (n₀ : ℂ) * ω) c' := by
  intro D hS cc δ hC σ hσ c c' n₀ n h₀ hn hc hA
  obtain ⟨-, -, -, h4, h5, h6, h7⟩ := hS cc δ hC ⊤ σ hσ IntermediateField.mem_top IntermediateField.mem_top
  obtain ⟨k, hk, hkc⟩ := hc
  have e₀ : (n₀ : ℂ) ≠ 0 := by exact_mod_cast h₀.ne'
  have e₁ : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold Adp1 at hA ⊢
  have a1 : ((k * n₀ : ℕ) : ℂ) * (c / (n₀ : ℂ)) ∈ lamOf D cc δ := by
    have : ((k * n₀ : ℕ) : ℂ) * (c / (n₀ : ℂ)) = (k : ℂ) * c := by
      push_cast; field_simp
    rw [this]; exact hkc
  have a2 := (h6 _ _ _ hA).1 a1
  have a3 : ((k * n₀ * n : ℕ) : ℂ) * (c' / ((n₀ * n : ℕ) : ℂ)) ∈ lamConj ⊤ σ (lamOf D cc δ) := by
    have : ((k * n₀ * n : ℕ) : ℂ) * (c' / ((n₀ * n : ℕ) : ℂ)) = ((k * n₀ : ℕ) : ℂ) * (c' / (n₀ : ℂ)) := by
      push_cast; field_simp
    rw [this]; exact a2
  obtain ⟨u, -, hu⟩ := h7 (k * n₀ * n) (by positivity)
    (fun _ _ _ => ⟨IntermediateField.mem_top, IntermediateField.mem_top⟩) _ a3
  have b1 := h5 (n : 𝓞 D.host.K) _ _ hu
  have b2 := h5 (-1 : 𝓞 D.host.K) _ _ hA
  have c1 : D.host.φ₀ ((((n : 𝓞 D.host.K) : D.host.K) : D.host.E)) = (n : ℂ) := by simp
  have c2 : D.host.φ₀ ((((-1 : 𝓞 D.host.K) : D.host.K) : D.host.E)) = (-1 : ℂ) := by simp
  rw [c1] at b1
  rw [c2] at b2
  have b3 := h4 _ _ _ _ b1 b2
  have z : (n : ℂ) * (c' / ((n₀ * n : ℕ) : ℂ)) + -1 * (c' / (n₀ : ℂ)) = 0 := by
    push_cast; field_simp; ring
  rw [z] at b3
  have b4 := (h6 1 _ _ b3).2 (by simp)
  rw [Nat.cast_one, one_mul] at b4
  refine ⟨_, b4, ?_⟩
  have : (c + (n₀ : ℂ) * ((n : ℂ) * u + -1 * (c / (n₀ : ℂ)))) / ((n₀ * n : ℕ) : ℂ) = u := by
    push_cast; field_simp; ring
  rw [this]; exact hu

end GlobalTheory.GalTheta
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

namespace GlobalTheory.GalThetaSign

theorem sign_eq {p k k' : ℕ} {m m' : ℤ} {q : ℝ} (hp : Odd p) (h : (p : ℝ) ^ k * q = (m : ℝ))
    (h' : (p : ℝ) ^ k' * q = (m' : ℝ)) : (-1 : ℂ) ^ m' = (-1 : ℂ) ^ m := by
  have key : ∀ {a a' : ℕ} {b b' : ℤ}, a ≤ a' → (p : ℝ) ^ a * q = (b : ℝ) → (p : ℝ) ^ a' * q = (b' : ℝ) →
      (-1 : ℂ) ^ b' = (-1 : ℂ) ^ b := by
    intro a a' b b' hle hb hb'
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hle
    have hr : (b' : ℝ) = ((p : ℤ) ^ j * b : ℤ) := by
      rw [← hb', Int.cast_mul, Int.cast_pow, Int.cast_natCast, ← hb, pow_add]
      ring
    have hi : b' = (p : ℤ) ^ j * b := by exact_mod_cast hr
    have hoddp : Odd ((p : ℤ) ^ j) := (by exact_mod_cast hp : Odd (p : ℤ)).pow
    have hev : Even (b' - b) := by
      rw [hi, show (p : ℤ) ^ j * b - b = ((p : ℤ) ^ j - 1) * b by ring]
      exact (hoddp.sub_odd odd_one).mul_right b
    rw [show b' = b + (b' - b) by ring, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), hev.neg_one_zpow, mul_one]
  rcases le_total k k' with hle | hle
  · exact key hle h h'
  · exact (key hle h' h).symm

theorem wPh_eq (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') {p k : ℕ} {m : ℤ} (hp : p.Prime) (h2 : p ≠ 2)
    (h : (p : ℝ) ^ k * qH D T x = (m : ℝ)) : wPh D T p x = (-1 : ℂ) ^ m := by
  have hodd : Odd p := hp.odd_of_ne_two h2
  rw [wPh, if_neg h2]
  have hex : ∃ s : ℂ, ∃ (k : ℕ) (m : ℤ), (p : ℝ) ^ k * qH D T x = (m : ℝ) ∧ s = (-1 : ℂ) ^ m :=
    ⟨_, k, m, h, rfl⟩
  obtain ⟨k0, m0, h0, hs⟩ := Classical.epsilon_spec hex
  rw [hs]
  exact sign_eq hodd h h0

theorem ee_half_pow (q : ℝ) (n : ℕ) :
    ee (q / 2) ^ n = Complex.exp ((((n : ℝ) * q : ℝ) : ℂ) * ((Real.pi : ℂ) * Complex.I)) := by
  rw [ee, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem exp_int_pi (m : ℤ) : Complex.exp ((m : ℂ) * ((Real.pi : ℂ) * Complex.I)) = (-1 : ℂ) ^ m := by
  rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]

theorem cj_top_pow (σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (z : ℂ) (n : ℕ) :
    cj ⊤ σ (z ^ n) = cj ⊤ σ z ^ n := by
  have hl : ∀ w : ℂ, liftM ⊤ w = (⟨w, IntermediateField.mem_top⟩ : (⊤ : IntermediateField ℚ ℂ)) :=
    fun w => dif_pos IntermediateField.mem_top
  simp only [cj]
  rw [hl, hl, ← map_pow]
  congr 1

theorem cj_top_sign (σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (m : ℤ) :
    cj ⊤ σ ((-1 : ℂ) ^ m) = (-1 : ℂ) ^ m := by
  have hl : ∀ w : ℂ, liftM ⊤ w = (⟨w, IntermediateField.mem_top⟩ : (⊤ : IntermediateField ℚ ℂ)) :=
    fun w => dif_pos IntermediateField.mem_top
  have he : (⟨(-1 : ℂ) ^ m, IntermediateField.mem_top⟩ : (⊤ : IntermediateField ℚ ℂ)) = (-1) ^ m := by
    apply Subtype.ext
    change (-1 : ℂ) ^ m = (⊤ : IntermediateField ℚ ℂ).val ((-1) ^ m)
    rw [map_zpow₀, map_neg, map_one]
  simp only [cj]
  rw [hl, he, map_zpow₀, map_neg, map_one]

theorem wPh_conj : ∀ (D : D7) (T T' : Tor D) (N N' : ℕ) (x x' : VC D N N') (σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (p k : ℕ) (m : ℤ), p.Prime → p ≠ 2 → (p : ℝ) ^ k * qH D T x = (m : ℝ) → cj ⊤ σ (wdPh D T x) = wdPh D T' x' → wPh D T p x = (-1 : ℂ) ^ m ∧ wPh D T' p x' = (-1 : ℂ) ^ m := by
  intro D T T' N N' x x' σ p k m hp h2 h hcj
  refine ⟨wPh_eq D T x hp h2 h, ?_⟩
  have h1 : wdPh D T x ^ (p ^ k) = (-1 : ℂ) ^ m := by
    rw [wdPh, ee_half_pow, Nat.cast_pow, h, ← exp_int_pi m, Complex.ofReal_intCast]
  have h3 : wdPh D T' x' ^ (p ^ k) = (-1 : ℂ) ^ m := by
    rw [← hcj, ← cj_top_pow, h1, cj_top_sign]
  rw [wdPh, ee_half_pow, ← exp_int_pi m, Complex.exp_eq_exp_iff_exists_int] at h3
  obtain ⟨l, hl⟩ := h3
  have hπ : (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero
  have hreal : (p : ℝ) ^ k * qH D T' x' = ((m + 2 * l : ℤ) : ℝ) := by
    have hc : (((p : ℝ) ^ k * qH D T' x' : ℝ) : ℂ) = (((m + 2 * l : ℤ) : ℝ) : ℂ) := by
      apply mul_right_cancel₀ hπ
      push_cast at hl ⊢
      linear_combination hl
    exact Complex.ofReal_injective hc
  rw [wPh_eq D T' x' hp h2 hreal, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), (even_two_mul l).neg_one_zpow, mul_one]

end GlobalTheory.GalThetaSign
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Nat

namespace GlobalTheory.IdealIdele

theorem pow_factorial_mul {M : Type} [Monoid M] [Fintype M] (a : M) (t : ℕ) (ht : 0 < t) :
    a ^ ((Fintype.card M)! * t) = a ^ (Fintype.card M)! := by
  obtain ⟨i, j, hij, hj, e⟩ : ∃ i j : ℕ, i < j ∧ j ≤ Fintype.card M ∧ a ^ i = a ^ j := by
    obtain ⟨i, j, hne, e⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin (Fintype.card M + 1) => a ^ (i : ℕ)) (by simp)
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨i, j, h, Nat.lt_succ_iff.1 j.2, e⟩
    · exact ⟨j, i, h, Nat.lt_succ_iff.1 i.2, e.symm⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij.le
  have hd : 0 < d := by omega
  have key : ∀ u : ℕ, a ^ (i + d * u) = a ^ i := by
    intro u
    induction u with
    | zero => simp
    | succ u ih => rw [Nat.mul_succ, ← add_assoc, pow_add, ih, ← pow_add, ← e]
  obtain ⟨c, hc⟩ : d ∣ (Fintype.card M)! := Nat.dvd_factorial hd (by omega)
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le
    (show i ≤ (Fintype.card M)! from le_trans (by omega) (Nat.self_le_factorial _))
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  have : (Fintype.card M)! * t.succ = i + d * (c * t) + s := by
    rw [Nat.mul_succ, ← mul_assoc, ← hc]; omega
  rw [this, pow_add, key, ← pow_add, ← hs]

theorem int_dvd_pow_sub (m N t : ℕ) (hN : 0 < N) (ht : 0 < t) :
    ∃ c : ℤ, (m : ℤ) ^ (N ! * t) = (m : ℤ) ^ N ! + N * c := by
  haveI : NeZero N := ⟨hN.ne'⟩
  have h := pow_factorial_mul (m : ZMod N) t ht
  rw [ZMod.card] at h
  obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd ((m : ℤ) ^ (N ! * t) - (m : ℤ) ^ N !) N).1
    (by push_cast; rw [h, sub_self])
  exact ⟨c, by linear_combination hc⟩

section Abstract

variable {A : Type} [CommRing A] (S : Subring A)

theorem exists_idem
    (hsep : ∀ y : A, (∀ N : ℕ, 0 < N → ∃ w ∈ S, y = (N : A) * w) → y = 0)
    (hcpl : ∀ x : ℕ → A, (∀ N, x N ∈ S) →
      (∀ N m : ℕ, 0 < N → 0 < m → ∃ w ∈ S, x (N * m) = x N + (N : A) * w) →
      ∃ y ∈ S, ∀ N : ℕ, 0 < N → ∃ w ∈ S, y = x N + (N : A) * w)
    (m : ℕ) (hm : 0 < m) :
    ∃ f ∈ S, f * f = f ∧ (∃ w ∈ S, f = (m : A) * w) ∧
      ∀ n : ℕ, 0 < n → m.Coprime n → ∃ w ∈ S, 1 - f = (n : A) * w := by
  have hc : ∀ N t : ℕ, 0 < N → 0 < t →
      ∃ c : ℤ, (m : A) ^ (N ! * t) = (m : A) ^ N ! + N * c := fun N t hN ht => by
    obtain ⟨c, h⟩ := int_dvd_pow_sub m N t hN ht
    refine ⟨c, ?_⟩
    have := congrArg (Int.cast : ℤ → A) h
    push_cast at this
    exact this
  have hx : ∀ k : ℕ, (m : A) ^ k ∈ S := fun k => pow_mem (natCast_mem S m) k
  obtain ⟨f, hf, h⟩ := hcpl (fun N => (m : A) ^ N !) (fun N => hx _) (by
    intro N k hN hk
    obtain ⟨t, ht⟩ := Nat.factorial_dvd_factorial (Nat.le_mul_of_pos_right N hk)
    have ht0 : 0 < t := Nat.pos_of_ne_zero (by
      rintro rfl
      exact (Nat.factorial_ne_zero _) (by simpa using ht))
    obtain ⟨c, hc⟩ := hc N t hN ht0
    exact ⟨c, intCast_mem S c, by simp only [ht, hc]⟩)
  refine ⟨f, hf, ?_, ?_, fun n hn hmn => ?_⟩
  · rw [← sub_eq_zero]
    refine hsep _ fun N hN => ?_
    obtain ⟨w, hw, hh⟩ := h N hN
    obtain ⟨c, hc⟩ := hc N 2 hN two_pos
    refine ⟨c + (2 * (m : A) ^ N ! * w + N * w * w - w), ?_, ?_⟩
    · exact add_mem (intCast_mem S c) (sub_mem (add_mem (mul_mem (mul_mem (ofNat_mem _ 2) (hx _)) hw)
        (mul_mem (mul_mem (natCast_mem _ _) hw) hw)) hw)
    · rw [pow_mul] at hc
      rw [hh]; linear_combination hc
  · obtain ⟨w, hw, hh⟩ := h m hm
    obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.factorial_ne_zero m)
    refine ⟨(m : A) ^ s + w, add_mem (hx s) hw, ?_⟩
    rw [hh, hs, pow_succ]; ring
  · obtain ⟨w, hw, hh⟩ := h n hn
    obtain ⟨t, ht⟩ := Nat.dvd_factorial (Nat.totient_pos.2 hn) (Nat.totient_le n)
    have h1 : m ^ n ! ≡ 1 [MOD n] := by
      have := (Nat.ModEq.pow_totient hmn).pow t
      rwa [← pow_mul, ← ht, one_pow] at this
    obtain ⟨c, hc⟩ := h1.dvd
    have hc' := congrArg (Int.cast : ℤ → A) hc
    push_cast at hc'
    refine ⟨c - w, sub_mem (intCast_mem S c) hw, ?_⟩
    rw [hh]; linear_combination hc'

end Abstract

theorem exists_local_generator {E : Type} [Field E] [NumberField E] (B : Ideal (𝓞 E)) (hB : B ≠ ⊥) :
    ∃ (m n : ℕ) (β : 𝓞 E), 0 < m ∧ 0 < n ∧ m.Coprime n ∧ (m : 𝓞 E) ∈ B ∧ β ∈ B ∧ β ≠ 0 ∧
      ∀ b ∈ B, β ∣ (n : 𝓞 E) * b := by
  set m := 2 * Ideal.absNorm B with hm
  have hN : 0 < Ideal.absNorm B := Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using hB)
  have hm2 : 2 ≤ m := by omega
  have hmB : (m : 𝓞 E) ∈ B := by
    rw [hm, Nat.cast_mul]; exact Ideal.mul_mem_left _ _ (Ideal.absNorm_mem B)
  have hm0 : (m : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨β, hβ⟩ := IsDedekindDomain.exists_sup_span_eq (I := B * Ideal.span {(m : 𝓞 E)}) (J := B)
    Ideal.mul_le_left (mul_ne_zero hB (by simpa using hm0))
  have hβB : β ∈ B := hβ ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self β)
  obtain ⟨C, hC⟩ : B ∣ Ideal.span {β} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hβB)
  have hsup : Ideal.span {(m : 𝓞 E)} ⊔ C = ⊤ := by
    apply mul_left_cancel₀ hB
    rw [Ideal.mul_sup, ← hC, hβ, Ideal.mul_top]
  have hC0 : C ≠ ⊥ := by
    rintro rfl
    rw [sup_bot_eq, Ideal.span_singleton_eq_top] at hsup
    have h1 := Ideal.absNorm_eq_one_iff.2 (Ideal.span_singleton_eq_top.2 hsup)
    rw [Ideal.absNorm_span_natCast] at h1
    have h2 := (Nat.pow_eq_one.1 h1).resolve_left (by omega)
    exact Module.finrank_pos.ne' h2
  have hβ0 : β ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hB hC0 (by rw [← hC]; simp)
  haveI : Finite (𝓞 E ⧸ C) := Ideal.finiteQuotientOfFreeOfNeBot C hC0
  have hu : IsUnit (Ideal.Quotient.mk C (m : 𝓞 E)) := by
    obtain ⟨x, hx, c, hc, e⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hsup)
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk C a) ?_
    rw [← map_mul, ← map_one (Ideal.Quotient.mk C), Ideal.Quotient.eq]
    rw [show (m : 𝓞 E) * a - 1 = -c by linear_combination e]
    exact neg_mem hc
  obtain ⟨k, hk, e⟩ := isOfFinOrder_iff_pow_eq_one.1 (isOfFinOrder_of_finite hu.unit)
  have e' : (m : 𝓞 E) ^ k - 1 ∈ C := by
    rw [← Ideal.Quotient.eq, map_pow, map_one]
    simpa using congrArg Units.val e
  have h1 : 1 < m ^ k := Nat.one_lt_pow hk.ne' (by omega)
  refine ⟨m, m ^ k - 1, β, by omega, by omega, ?_, hmB, hβB, hβ0, fun b hb => ?_⟩
  · refine Nat.Coprime.of_dvd_left (dvd_pow_self m hk.ne') ?_
    exact (Nat.coprime_self_sub_right h1.le).2 (Nat.coprime_one_right _)
  · rw [← Ideal.mem_span_singleton, hC, mul_comm (((m ^ k - 1 : ℕ)) : 𝓞 E)]
    refine Ideal.mul_mem_mul hb ?_
    rw [Nat.cast_sub h1.le]
    push_cast
    exact e'

theorem exists_idele_generator : ∀ (D : D7) (B : Ideal (𝓞 D.host.E)), B ≠ ⊥ → ∃ y : (AE D)ˣ, (∀ b ∈ B, ((y⁻¹ : (AE D)ˣ) : AE D) * inc D (b : D.host.E) ∈ OhE D) ∧ ∃ (k : ℕ) (b : Fin k → 𝓞 D.host.E) (w : Fin k → AE D), (∀ i, b i ∈ B) ∧ (∀ i, w i ∈ OhE D) ∧ (y : AE D) = ∑ i, inc D (b i : D.host.E) * w i := by
  intro D B hB
  obtain ⟨m, n, β, hm, hn, hmn, hmB, hβB, hβ0, hdvd⟩ := exists_local_generator B hB
  obtain ⟨hsep, hcpl⟩ := GlobalTheory.IntAdeleComplete.integral_separated_complete D
  obtain ⟨f, hf, hff, ⟨w, hw, hfw⟩, h3⟩ := exists_idem (OhE D) hsep hcpl m hm
  obtain ⟨v, hv, hfv⟩ := h3 n hn hmn
  have hint : ∀ b : 𝓞 D.host.E, inc D (b : D.host.E) ∈ OhE D := fun b =>
    (GlobalTheory.HeckeVal.inc_mem_iff D _).2 b.isIntegral_coe
  have hβE : (β : D.host.E) ≠ 0 := by simpa using hβ0
  have hinv : inc D (β : D.host.E) * inc D (β : D.host.E)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hβE, map_one]
  have hy : ((1 - f) * inc D (β : D.host.E) + f) * ((1 - f) * inc D (β : D.host.E)⁻¹ + f) = 1 := by
    linear_combination (1 - f) ^ 2 * hinv +
      (2 - inc D (β : D.host.E) - inc D (β : D.host.E)⁻¹) * hff
  refine ⟨⟨_, _, hy, by rw [mul_comm, hy]⟩, fun b hb => ?_, 2, ![β, m], ![1 - f, w], ?_, ?_, ?_⟩
  · obtain ⟨d, hd⟩ := hdvd b hb
    have hd' : (n : AE D) * inc D (b : D.host.E) = inc D (β : D.host.E) * inc D (d : D.host.E) := by
      rw [← map_natCast (inc D), ← map_mul, ← map_mul]
      congr 1
      exact_mod_cast congrArg (fun x : 𝓞 D.host.E => (x : D.host.E)) hd
    change ((1 - f) * inc D (β : D.host.E)⁻¹ + f) * inc D (b : D.host.E) ∈ OhE D
    rw [show ((1 - f) * inc D (β : D.host.E)⁻¹ + f) * inc D (b : D.host.E) =
      v * inc D (d : D.host.E) + f * inc D (b : D.host.E) by
        rw [hfv]
        linear_combination v * inc D (β : D.host.E)⁻¹ * hd' + v * inc D (d : D.host.E) * hinv]
    exact add_mem (mul_mem hv (hint d)) (mul_mem hf (hint b))
  · intro i
    fin_cases i
    · exact hβB
    · exact hmB
  · intro i
    fin_cases i
    · exact sub_mem (one_mem _) hf
    · exact hw
  · have : inc D (((m : 𝓞 D.host.E)) : D.host.E) = (m : AE D) := by
      rw [← map_natCast (inc D)]; congr 1
    change (1 - f) * inc D (β : D.host.E) + f = _
    rw [Fin.sum_univ_two]
    change _ = inc D (β : D.host.E) * (1 - f) + inc D (((m : 𝓞 D.host.E)) : D.host.E) * w
    rw [this, ← hfw]; ring

end GlobalTheory.IdealIdele
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.localBasisLattice_index_coprime : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' r : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (p : ℕ), p.Prime → (La D (tor0 D cc δ) L L').FG → LocBasis D p (YYl D L L') b → Nat.Coprime (((LaB D (tor0 D cc δ) b).addSubgroupOf (La D (tor0 D cc δ) L L')).index) p := by
  first | exact @GlobalTheory.NormSum.LocIndex.index_coprime | exact GlobalTheory.NormSum.LocIndex.index_coprime | (intros; apply GlobalTheory.NormSum.LocIndex.index_coprime <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.orthonormalBasis_galois_map : ∀ (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E), (∀ a : D.host.K, σ (a : D.host.E) = (a : D.host.E)) → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → OnB D (fun j => (b j).map σ) := by
  first | exact @GlobalTheory.NormSum.onB_map_aut | exact GlobalTheory.NormSum.onB_map_aut | (intros; apply GlobalTheory.NormSum.onB_map_aut <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_integer_map_eq_halfOneAddSqrt : ∀ (D : D7), ∃ a : 𝓞 D.host.K, D.host.φ₀ (((a : D.host.K) : D.host.E)) = w0 D := by
  first | exact @GlobalTheory.NormSum.exists_integer_map_eq_w0 | exact GlobalTheory.NormSum.exists_integer_map_eq_w0 | (intros; apply GlobalTheory.NormSum.exists_integer_map_eq_w0 <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.orthonormalTransition_det_mul_conj_eq_one : ∀ (D : D7), admG1 D → ∀ (N N' r : ℕ) (b₀ b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b₀ → OnB D b → (((Matrix.of fun i j => hYY D (b j) (b₀ i)).det : D.host.K) : D.host.E) * D.host.conj (((Matrix.of fun i j => hYY D (b j) (b₀ i)).det : D.host.K) : D.host.E) = 1 := by
  first | exact @GlobalTheory.NormSum.det_onB_mul_conj | exact GlobalTheory.NormSum.det_onB_mul_conj | (intros; apply GlobalTheory.NormSum.det_onB_mul_conj <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.meanSquare_orthoProductTheta_eq_prod : ∀ (D : D7) (T : Tor D) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ T.abelian₂ = AddSubgroup.closure {w₁, w₂}) → (∀ i j, coordB D T b i (embV D T (b j)) = if i = j then 1 else 0) → (∀ z : VC D N N', z = ∑ j, coordB D T b j z • embV D T (b j)) → ∀ g : ℂ → ℂ, Continuous g → (∀ ω ∈ T.abelian₂, ∀ z, ‖U1 T.abelian₂ ω g z‖ = ‖g z‖) → normSq D T (LaB D T b) (pullB D T b g) = nrm1Sq T.abelian₂ g ^ r := by
  first | exact @GlobalTheory.PullNorm.normSq_pullB | exact GlobalTheory.PullNorm.normSq_pullB | (intros; apply GlobalTheory.PullNorm.normSq_pullB <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

namespace GlobalTheory.ConjugateLattice

theorem lamConj_eq_closure_pair : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), g2 (lamOf D cc δ) ∈ M → g3 (lamOf D cc δ) ∈ M → ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ lamConj M ρ (lamOf D cc δ) = AddSubgroup.closure {w₁, w₂} := by
  intro D _ cc δ hc M ρ h2 h3
  obtain ⟨L, h⟩ := GlobalTheory.CurveLattice.exists_periodPair_lamOf D cc δ hc
  generalize lamOf D cc δ = Λ at h h2 h3
  obtain ⟨-, -, hd, -, -, -, hex⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L Λ h
  have hne : ρ (TaylorLogMetric.liftM M (g2 Λ)) ^ 3 - 27 * ρ (TaylorLogMetric.liftM M (g3 Λ)) ^ 2 ≠ 0 := by
    have e : ρ (TaylorLogMetric.liftM M (g2 Λ)) ^ 3 - 27 * ρ (TaylorLogMetric.liftM M (g3 Λ)) ^ 2 =
        ρ (TaylorLogMetric.liftM M (g2 Λ) ^ 3 - 27 * TaylorLogMetric.liftM M (g3 Λ) ^ 2) := by
      simp only [map_sub, map_mul, map_pow, map_ofNat]
    rw [e, map_ne_zero]
    intro h0
    apply hd
    have := congrArg (fun y : M => (y : ℂ)) h0
    simp only [TaylorLogMetric.liftM, dif_pos h2, dif_pos h3] at this
    exact this
  obtain ⟨L', ha, hb⟩ := hex _ _ hne
  obtain ⟨e2, e3, -, -, -, hun, -⟩ :=
    GlobalTheory.LatticeInvariants.invariants_dictionary L' L'.lattice.toAddSubgroup (fun _ => Iff.rfl)
  have hs := Classical.epsilon_spec (p := fun Λ' : AddSubgroup ℂ =>
    g2 Λ' = ρ (TaylorLogMetric.liftM M (g2 Λ)) ∧ g3 Λ' = ρ (TaylorLogMetric.liftM M (g3 Λ))) ⟨_, e2.trans ha, e3.trans hb⟩
  have hL : lamConj M ρ Λ = L'.lattice.toAddSubgroup :=
    hun _ (hs.1.trans (e2.trans ha).symm) (hs.2.trans (e3.trans hb).symm)
  refine ⟨L'.ω₁, L'.ω₂, L'.indep, ?_⟩
  rw [hL]
  ext z
  rw [Submodule.mem_toAddSubgroup, PeriodPair.mem_lattice, AddSubgroup.mem_closure_pair]
  simp only [zsmul_eq_mul]

end GlobalTheory.ConjugateLattice
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

theorem _root_.GlobalTheory.T.exists_cm_idempotents_select_conjugate_primes : ∀ (D : D7), ∃ e : ℕ → 𝓞 D.host.E, (∀ N m : ℕ, 0 < N → 0 < m → (N : 𝓞 D.host.E) ∣ e (N * m) - e N) ∧ (∀ N : ℕ, 0 < N → (N : 𝓞 D.host.E) ∣ e N * e N - e N ∧ (N : 𝓞 D.host.E) ∣ e N * (D.host.conj • e N)) ∧ ∀ q k : ℕ, q.Prime → (InertQ D q → ((q ^ k : ℕ) : 𝓞 D.host.E) ∣ e (q ^ k) + D.host.conj • e (q ^ k)) ∧ (¬ InertQ D q → ((q ^ k : ℕ) : 𝓞 D.host.E) ∣ 1 - (e (q ^ k) + D.host.conj • e (q ^ k))) := by
  first | exact @GlobalTheory.SelectIdem.exists_select_idem | exact GlobalTheory.SelectIdem.exists_select_idem | (intros; apply GlobalTheory.SelectIdem.exists_select_idem <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.unitaryHeckeCharacter_values : ∀ (D : D7) (N : ℕ) (χ : HeckeU D N) (x : (AE D)ˣ), Mod1All ((χ.f x : ℂˣ) : ℂ) ∧ (IntU D x → ∃ m : ℕ, 0 < m ∧ χ.f x ^ m = 1) ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), (∃ y : (AE D)ˣ, IntU D y ∧ ZeroAt D p (((x * y : (AE D)ˣ) : AE D) - 1)) → ‖lamC lam ((χ.f x : ℂˣ) : ℂ)‖ = 1 := by
  first | exact @GlobalTheory.HeckeVal.hecke_values | exact GlobalTheory.HeckeVal.hecke_values | (intros; apply GlobalTheory.HeckeVal.hecke_values <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.latticeInvariants_periodPair_dictionary : ∀ (L : PeriodPair) (Λ : AddSubgroup ℂ), (∀ z, z ∈ Λ ↔ z ∈ L.lattice) → g2 Λ = L.g₂ ∧ g3 Λ = L.g₃ ∧ TaylorLogMetric.discr Λ ≠ 0 ∧ area Λ = |(L.ω₁ * starRingEnd ℂ L.ω₂).im| ∧ (∀ z, z ∉ Λ → wpF Λ z = L.weierstrassP z ∧ wpD Λ z = L.derivWeierstrassP z) ∧ (∀ (Λ' : AddSubgroup ℂ), g2 Λ' = g2 Λ → g3 Λ' = g3 Λ → Λ' = Λ) ∧ ∀ a b : ℂ, a ^ 3 - 27 * b ^ 2 ≠ 0 → ∃ (L' : PeriodPair), L'.g₂ = a ∧ L'.g₃ = b := by
  first | exact @GlobalTheory.LatticeInvariants.invariants_dictionary | exact GlobalTheory.LatticeInvariants.invariants_dictionary | (intros; apply GlobalTheory.LatticeInvariants.invariants_dictionary <;> assumption)
end
