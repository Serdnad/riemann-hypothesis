module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle004
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015

@[expose] public section

section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private noncomputable def UpperTheory.Gal.W2.Seed.pDomSt_dL {I : Type} (a : I → ℂ) : (I → ℂ) →ₗ[ℝ] (I → ℂ) where
  toFun z k := a k * z k
  map_add' z w := by funext k; simp [mul_add]
  map_smul' r z := by funext k; simp [mul_left_comm]

private theorem UpperTheory.Gal.W2.Seed.pDomSt_theta_mul {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) {n : ℕ}
    (Θ : ℝ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℝ] (Phi A × Fin n → ℂ))
    (hΘ : ∀ (x : Fin n → 𝓞 E) τ i, Θ (1 ⊗ₜ x) (τ, i) = τ.1 (x i : E))
    (b : 𝓞 E) (M : ℝ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℝ] ℝ ⊗[ℤ] (Fin n → 𝓞 E))
    (hM : ∀ x : Fin n → 𝓞 E, M (1 ⊗ₜ x) = 1 ⊗ₜ (b • x)) (x : ℝ ⊗[ℤ] (Fin n → 𝓞 E)) (k : Phi A × Fin n) :
    Θ (M x) k = k.1.1 (b : E) * Θ x k := by
  obtain ⟨τ, i⟩ := k
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r y =>
    have h : r ⊗ₜ[ℤ] y = r • ((1 : ℝ) ⊗ₜ[ℤ] y) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, LinearMap.map_smul, hM, LinearEquiv.map_smul, LinearEquiv.map_smul, Pi.smul_apply, Pi.smul_apply,
      hΘ, hΘ, Complex.real_smul, Complex.real_smul]
    simp [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb, mul_add]

private theorem UpperTheory.Gal.W2.Seed.pDomSt_term (D H z : ℂ) (e : ℝ) (hD : D.re = 0) (hH : H.im = 0) :
    (D * H * ((e : ℂ) * Complex.I * z) * (starRingEnd ℂ) z).re = -D.im * H.re * e * Complex.normSq z := by
  have hD' : D = (D.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hD]
  have hH' : H = (H.re : ℂ) := by
    apply Complex.ext <;> simp [hH]
  have h1 : D * H * ((e : ℂ) * Complex.I * z) * (starRingEnd ℂ) z
      = D * H * e * Complex.I * (z * (starRingEnd ℂ) z) := by ring
  rw [h1, Complex.mul_conj, hD', hH']
  have h2 : (D.im : ℂ) * Complex.I * (H.re : ℂ) * (e : ℂ) * Complex.I * (Complex.normSq z : ℂ)
      = ((-D.im * H.re * e * Complex.normSq z : ℝ) : ℂ) := by
    push_cast
    linear_combination ((D.im : ℂ) * H.re * e * Complex.normSq z) * Complex.I_sq
  rw [h2, Complex.ofReal_re]
  simp

private theorem UpperTheory.Gal.W2.Seed.pDomSt_sum {I : Type} [Fintype I] [DecidableEq I] (k0 : I) (y : I → ℝ) :
    ∑ k, (if k = k0 then (1 : ℝ) else -1) * y k = 2 * y k0 - ∑ k, y k := by
  have h : ∀ k, (if k = k0 then (1 : ℝ) else -1) * y k = 2 * (if k = k0 then y k else 0) - y k := by
    intro k
    split_ifs <;> ring
  simp only [h, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem UpperTheory.Gal.W2.Seed.pDomSt :
    TraceType → RealIso → FormCoord → HdSign → DiagTrace → DomSt := by
  intro hT hR hF hS hD E _ _ _ A n hn
  classical
  obtain ⟨Θ, hΘ⟩ := hR E A n
  obtain ⟨-, hsum, -, him⟩ := hT E A
  let k0 : Phi A × Fin n := (⟨A.τ₀, rfl⟩, ⟨0, hn⟩)
  have hk0 : ∀ k : Phi A × Fin n,
      (InfinitePlace.mk k.1.1 = InfinitePlace.mk A.τ₀ ∧ (k.2 : ℕ) = 0) ↔ k = k0 := by
    rintro ⟨⟨τ, hτ⟩, i⟩
    constructor
    · rintro ⟨h1, h2⟩
      rcases InfinitePlace.mk_eq_iff.mp h1 with h | h
      · exact Prod.ext (Subtype.ext h) (Fin.ext h2)
      · exfalso
        apply him
        have h3 : A.τ₀ (A.ω : E) = (starRingEnd ℂ) (τ (A.ω : E)) := by
          rw [← h, ComplexEmbedding.conjugate_coe_eq]
        rw [hτ] at h3
        exact Complex.conj_eq_iff_im.mp h3.symm
    · intro h
      rw [h]
      exact ⟨rfl, rfl⟩
  let ε : Phi A × Fin n → ℝ := fun k => if k = k0 then 1 else -1
  let a : Phi A × Fin n → ℂ := fun k => (ε k : ℂ) * Complex.I
  have ha2 : ∀ k, a k * a k = -1 := by
    intro k
    have h' : (ε k : ℂ) * (ε k) = 1 := by
      simp only [ε]
      split_ifs <;> norm_num
    simp only [a]
    linear_combination Complex.I ^ 2 * h' + Complex.I_sq
  have hca : ∀ k, (starRingEnd ℂ) (a k) = -a k := by
    intro k
    simp only [a, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  let J := Θ.symm.toLinearMap ∘ₗ pDomSt_dL a ∘ₗ Θ.toLinearMap
  have hJ : ∀ x k, Θ (J x) k = a k * Θ x k := by
    intro x k
    simp [J, pDomSt_dL]
  have hpos : ∀ k : Phi A × Fin n, 0 < -(k.1.1 A.δ).im * ((k.1.1 (A.hd n k.2 : E)).re * ε k) := by
    intro k
    have h1 := A.δ_sign k.1.1 k.1.2
    obtain ⟨-, -, hp, hm⟩ := hS E A n k.1.1 k.2
    have h2 : 0 < (k.1.1 (A.hd n k.2 : E)).re * ε k := by
      by_cases hk : k = k0
      · have := hp ((hk0 k).mpr hk)
        rw [show ε k = 1 from if_pos hk, mul_one]
        exact this
      · have := hm (fun h => hk ((hk0 k).mp h))
        rw [show ε k = -1 from if_neg hk, mul_neg_one]
        linarith
    exact mul_pos (by linarith) h2
  refine ⟨J, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    apply Θ.injective
    funext k
    rw [hJ, hJ, map_neg, Pi.neg_apply, ← mul_assoc, ha2]
    ring
  · intro x y
    rw [hF E A n Θ hΘ, hF E A n Θ hΘ]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hJ, hJ, map_mul, hca]
    congr 2
    linear_combination (-(k.1.1 A.δ * k.1.1 (A.hd n k.2 : E) * Θ x k * (starRingEnd ℂ) (Θ y k))) * ha2 k
  · intro x hx
    rw [hF E A n Θ hΘ]
    have hx' : Θ x ≠ 0 := by simpa using hx
    obtain ⟨k1, hk1⟩ : ∃ k, Θ x k ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx' (funext h)
    have hterm : ∀ k : Phi A × Fin n,
        2 * (k.1.1 A.δ * k.1.1 (A.hd n k.2 : E) * Θ (J x) k * (starRingEnd ℂ) (Θ x k)).re
          = 2 * ((-(k.1.1 A.δ).im * ((k.1.1 (A.hd n k.2 : E)).re * ε k)) * Complex.normSq (Θ x k)) := by
      intro k
      obtain ⟨hH, hD0, -, -⟩ := hS E A n k.1.1 k.2
      rw [hJ]
      simp only [a]
      rw [pDomSt_term _ _ _ _ hD0 hH]
      ring
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    apply Finset.sum_pos'
    · intro k _
      exact mul_nonneg (by norm_num) (mul_nonneg (hpos k).le (Complex.normSq_nonneg _))
    · exact ⟨k1, Finset.mem_univ _, mul_pos (by norm_num) (mul_pos (hpos k1) (Complex.normSq_pos.mpr hk1))⟩
  · intro b M hM
    apply LinearMap.ext
    intro x
    apply Θ.injective
    funext k
    simp only [LinearMap.comp_apply]
    rw [hJ, pDomSt_theta_mul A Θ hΘ b M hM, pDomSt_theta_mul A Θ hΘ b M hM, hJ]
    ring
  · intro c M hM
    dsimp only
    have htrM : LinearMap.trace ℝ _ M = 2 * (∑ k : Phi A × Fin n, k.1.1 (c : E)).re := by
      rw [← LinearMap.trace_conj' M Θ]
      refine hD _ (fun k : Phi A × Fin n => k.1.1 (c : E)) _ (fun z k => ?_)
      rw [LinearEquiv.conj_apply_apply, pDomSt_theta_mul A Θ hΘ c M hM, LinearEquiv.apply_symm_apply]
    have htrJM : LinearMap.trace ℝ _ (J ∘ₗ M) = 2 * (∑ k : Phi A × Fin n, a k * k.1.1 (c : E)).re := by
      rw [← LinearMap.trace_conj' (J ∘ₗ M) Θ]
      refine hD _ (fun k : Phi A × Fin n => a k * k.1.1 (c : E)) _ (fun z k => ?_)
      rw [LinearEquiv.conj_apply_apply, LinearMap.comp_apply, hJ, pDomSt_theta_mul A Θ hΘ c M hM,
        LinearEquiv.apply_symm_apply]
      ring
    have hre : (∑ k : Phi A × Fin n, a k * k.1.1 (c : E)).re = -∑ k, ε k * (k.1.1 (c : E)).im := by
      rw [Complex.re_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp [a, Complex.mul_re]
    rw [hsum (fun τ => (n : ℂ) * τ (c : E))]
    constructor
    · rw [htrM]
      simp [ComplexEmbedding.conjugate_coe_eq, Fintype.sum_prod_type, Complex.re_sum, Finset.mul_sum]
    · rw [htrJM, hre, pDomSt_sum k0 (fun k => (k.1.1 (c : E)).im)]
      simp [k0, ComplexEmbedding.conjugate_coe_eq, Fintype.sum_prod_type, Complex.im_sum, Finset.mul_sum]
      ring
end

section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed.QuadraticExtensions

private lemma sq_in_Zq (q : ℕ) [Fact q.Prime] (d g d0 : ℕ) (hg : 0 < g) (hd : g ^ 2 * d0 = d)
    (h : IsSquare (-(d : ℚ_[q]))) : ∃ z : ℤ_[q], z ^ 2 = -(d0 : ℤ_[q]) := by
  obtain ⟨y, hy⟩ := h
  have hg0 : (g : ℚ_[q]) ≠ 0 := by exact_mod_cast hg.ne'
  have hd' : (d : ℚ_[q]) = (g : ℚ_[q]) ^ 2 * d0 := by rw [← hd]; push_cast; ring
  rw [hd'] at hy
  have hx : (y / g) ^ 2 = -(d0 : ℚ_[q]) := by
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hg0)]
    linear_combination -hy
  have hxn : ‖y / (g : ℚ_[q])‖ ≤ 1 := by
    have h1 : ‖y / (g : ℚ_[q])‖ ^ 2 ≤ 1 := by
      rw [← norm_pow, hx, norm_neg]
      have : ‖((d0 : ℤ_[q]) : ℚ_[q])‖ ≤ 1 := PadicInt.norm_le_one _
      simpa using this
    by_contra hc
    push_neg at hc
    nlinarith
  let z : ℤ_[q] := ⟨y / g, hxn⟩
  have hzc : (z : ℚ_[q]) = y / g := rfl
  refine ⟨z, ?_⟩
  have hc : ((z ^ 2 : ℤ_[q]) : ℚ_[q]) = ((-(d0 : ℤ_[q]) : ℤ_[q]) : ℚ_[q]) := by
    push_cast
    rw [hzc]
    exact hx
  first
    | exact PadicInt.ext hc
    | exact Subtype.ext hc
    | exact PadicInt.coe_injective hc

private lemma not_dvd (q : ℕ) [hq : Fact q.Prime] (d0 : ℕ) (hsq : Squarefree d0) (z : ℤ_[q])
    (hz : z ^ 2 = -(d0 : ℤ_[q])) : ¬ q ∣ d0 := by
  intro hdvd
  have hnorm : ‖z‖ ^ 2 = ‖((d0 : ℤ) : ℤ_[q])‖ := by
    rw [← norm_pow, hz, norm_neg, Int.cast_natCast]
  have hd1 : ‖((d0 : ℤ) : ℤ_[q])‖ < 1 :=
    (PadicInt.norm_int_lt_one_iff_dvd _).mpr (by exact_mod_cast hdvd)
  have hz1 : ‖z‖ < 1 := by
    by_contra hc
    push_neg at hc
    nlinarith [norm_nonneg z]
  obtain ⟨w, rfl⟩ := (PadicInt.norm_lt_one_iff_dvd z).mp hz1
  have hle : ‖((d0 : ℤ) : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(2 : ℕ) : ℤ) := by
    rw [← hnorm, norm_mul, PadicInt.norm_p, mul_pow]
    have hw := PadicInt.norm_le_one w
    have he : (q : ℝ) ^ (-(2 : ℕ) : ℤ) = ((q : ℝ)⁻¹) ^ 2 := by
      rw [_root_.zpow_neg, zpow_natCast, inv_pow]
    rw [he]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg w) hw)
  have h2 := PadicInt.norm_int_le_pow_iff_dvd.mp hle
  have h3 : q ^ 2 ∣ d0 := by exact_mod_cast h2
  rw [sq] at h3
  exact (Nat.Prime.one_lt hq.out).ne' (Nat.isUnit_iff.mp (hsq q h3))

private lemma root_mod (q : ℕ) [Fact q.Prime] (d0 : ℕ) (z : ℤ_[q])
    (hz : z ^ 2 = -(d0 : ℤ_[q])) : ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 + d0 := by
  refine ⟨((PadicInt.toZMod z).val : ℤ), ?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).1
  have h := congrArg (PadicInt.toZMod (p := q)) hz
  simp only [map_pow, map_neg, map_natCast] at h
  push_cast
  rw [ZMod.natCast_zmod_val, h]
  ring

private lemma two_case [Fact (Nat.Prime 2)] (d0 : ℕ) (hodd : ¬ 2 ∣ d0) (z : ℤ_[2])
    (hz : z ^ 2 = -(d0 : ℤ_[2])) : d0 % 8 = 7 := by
  have h := congrArg (PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod (2 ^ 3)) hz
  rw [map_pow, map_neg, map_natCast] at h
  generalize (PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod (2 ^ 3)) z = a at h
  revert a
  show ∀ a : ZMod 8, a ^ 2 = -((d0 : ZMod 8)) → d0 % 8 = 7
  rw [← ZMod.natCast_mod d0 8]
  have hlt := Nat.mod_lt d0 (by norm_num : 8 > 0)
  have hodd : d0 % 2 = 1 := by omega
  interval_cases h8 : d0 % 8
  all_goals first | omega | decide

private lemma not_dvd_four (q : ℕ) (hq : q.Prime) (h2 : q ≠ 2) : ¬ (q : ℤ) ∣ 4 := by
  intro h
  have h' : q ∣ 2 ^ 2 := by exact_mod_cast h
  exact h2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h'))

private lemma root_odd (q : ℕ) (hq : q.Prime) (h2 : q ≠ 2) (d0 m : ℕ) (hm : d0 + 1 = 4 * m) (r0 : ℤ)
    (hr : (q : ℤ) ∣ r0 ^ 2 + d0) : ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - 1 * r + m := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, q + 1 = 2 * k := by
    rcases hq.eq_two_or_odd' with h | ⟨j, hj⟩
    · exact absurd h h2
    · exact ⟨j + 1, by omega⟩
  refine ⟨(r0 + 1) * k, ?_⟩
  have hpz : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have h4 : (q : ℤ) ∣ 4 * (((r0 + 1) * k) ^ 2 - 1 * ((r0 + 1) * k) + m) := by
    obtain ⟨c, hc⟩ := hr
    have hk' : (2 * k : ℤ) = q + 1 := by exact_mod_cast hk.symm
    have hm' : (4 * m : ℤ) = d0 + 1 := by exact_mod_cast hm.symm
    refine ⟨c + (r0 + 1) * (2 * r0 + (r0 + 1) * q), ?_⟩
    linear_combination ((r0 + 1) ^ 2 * (2 * (k : ℤ) + q + 1) - 2 * (r0 + 1)) * hk' + hm' + hc
  rcases hpz.dvd_or_dvd h4 with h | h
  · exact absurd h (not_dvd_four q hq h2)
  · exact h

end UpperTheory.Gal.W2.Seed.QuadraticExtensions

open UpperTheory.Gal.W2.Seed.QuadraticExtensions in
theorem UpperTheory.Gal.W2.Seed.pQuadEx :
    QuadEx := by
  intro d hd
  obtain ⟨d0, g, hgd, hsq⟩ := Nat.sq_mul_squarefree d
  have hg : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h | h
    · subst h; simp at hgd; omega
    · exact h
  have hd0 : 0 < d0 := by
    rcases Nat.eq_zero_or_pos d0 with h | h
    · subst h; simp at hgd; omega
    · exact h
  have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  have hdq : (d : ℚ) = (g : ℚ) ^ 2 * d0 := by rw [← hgd]; push_cast; ring
  by_cases h43 : d0 % 4 = 3
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, d0 + 1 = 4 * m := ⟨(d0 + 1) / 4, by omega⟩
    have hdisc : (1 : ℤ) ^ 2 - 4 * (m : ℤ) = -(d0 : ℤ) := by
      have : ((d0 : ℤ) + 1) = 4 * (m : ℤ) := by exact_mod_cast hm
      linarith
    refine ⟨1, m, 1 / (g : ℚ), ?_, ?_, ?_⟩
    · rw [hdisc]; omega
    · rw [hdisc, hdq]; push_cast; field_simp
    · intro q _ hsqr
      obtain ⟨z, hz⟩ := sq_in_Zq q d g d0 hg hgd hsqr
      have hnd := not_dvd q d0 hsq z hz
      refine ⟨?_, ?_⟩
      · rw [hdisc, dvd_neg]
        intro h
        exact hnd (by exact_mod_cast h)
      · by_cases hq2 : q = 2
        · subst hq2
          have h7 := two_case d0 hnd z hz
          refine ⟨0, ?_⟩
          have : (m : ℤ) % 2 = 0 := by omega
          push_cast
          omega
        · obtain ⟨r0, hr0⟩ := root_mod q d0 z hz
          exact root_odd q (Fact.out) hq2 d0 m hm r0 hr0
  · refine ⟨0, d0, 2 / (g : ℚ), ?_, ?_, ?_⟩
    · omega
    · rw [hdq]; push_cast; field_simp; ring
    · intro q _ hsqr
      obtain ⟨z, hz⟩ := sq_in_Zq q d g d0 hg hgd hsqr
      have hnd := not_dvd q d0 hsq z hz
      refine ⟨?_, ?_⟩
      · by_cases hq2 : q = 2
        · subst hq2
          have h7 := two_case d0 hnd z hz
          omega
        · have hq : q.Prime := Fact.out
          have hpz : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
          intro h
          have h' : (q : ℤ) ∣ 4 * (d0 : ℤ) := by
            have : (0 : ℤ) ^ 2 - 4 * (d0 : ℤ) = -(4 * (d0 : ℤ)) := by ring
            rw [this, dvd_neg] at h
            exact h
          rcases hpz.dvd_or_dvd h' with h4 | h4
          · exact not_dvd_four q hq hq2 h4
          · exact hnd (by exact_mod_cast h4)
      · obtain ⟨r0, hr0⟩ := root_mod q d0 z hz
        exact ⟨r0, by simpa using hr0⟩
end

section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private theorem trace_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (z : E) :
    Algebra.trace ℚ E (IsCMField.complexConj E z) = Algebra.trace ℚ E z :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) z

private theorem hd_bar {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (i : Fin n) :
    A.bar (A.hd n i) = A.hd n i := by
  unfold Arith.hd Arith.dg
  split_ifs <;> simp [A.c_real]

private theorem hd_ne {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (i : Fin n) :
    ((A.hd n i : 𝓞 E) : E) ≠ 0 := by
  have := A.c_ne
  unfold Arith.hd Arith.dg
  split_ifs <;> simp [this]

private theorem delta_ne {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) : A.δ ≠ 0 := by
  intro h
  have := A.δ_sign A.τ₀ rfl
  simp [h] at this

private theorem alternatingMap_sub_base_eq_alternating_sum_removeNth {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ)
    (x : Fin n → 𝓞 E) : A.EF n x x = 0 := by
  rw [Arith.EF_apply]
  set s : 𝓞 E := ∑ i, A.hd n i * x i * A.bar (x i) with hs
  have hbs : A.bar s = s := by

    rw [hs, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, hd_bar, A.bar_bar]
    ring
  have hc : IsCMField.complexConj E ((s : 𝓞 E) : E) = (s : E) := by
    rw [← A.bar_eq, hbs]
  have h1 : Algebra.trace ℚ E (A.δ * (s : E)) = - Algebra.trace ℚ E (A.δ * (s : E)) := by
    conv_lhs => rw [← trace_cj, map_mul, A.δ_im, hc, neg_mul, map_neg]
  have h2 : ((A.trd s : ℤ) : ℚ) = 0 := by
    rw [A.trd_spec]
    linarith
  exact_mod_cast h2

private theorem laurent_adjoin_eq_of_image_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) :
    Function.Injective (A.EF n) := by
  refine (injective_iff_map_eq_zero (A.EF n)).2 fun x hx => ?_
  funext i
  by_contra hne
  have hxi : ((x i : 𝓞 E) : E) ≠ 0 := by
    intro h
    exact hne (RingOfIntegers.coe_eq_zero_iff.1 h)
  have hw : A.δ * ((A.hd n i : 𝓞 E) : E) * (x i : E) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (delta_ne A) (hd_ne A n i)) hxi
  have hint : ∀ b : 𝓞 E, Algebra.trace ℚ E (A.δ * ((A.hd n i : 𝓞 E) : E) * (x i : E) * (b : E)) = 0 := by
    intro b
    have h0 : A.EF n x (Pi.single i (A.bar b)) = 0 := by rw [hx]; rfl
    rw [Arith.EF_apply] at h0
    have h1 : (∑ j, A.hd n j * x j * A.bar ((Pi.single i (A.bar b) : Fin n → 𝓞 E) j)) =
        A.hd n i * x i * b := by
      rw [Finset.sum_eq_single i]
      · simp [A.bar_bar]
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · simp
    rw [h1] at h0
    have h2 := A.trd_spec (A.hd n i * x i * b)
    rw [h0] at h2
    simp only [Int.cast_zero] at h2
    rw [h2]
    congr 1
    push_cast
    ring
  obtain ⟨b, hb⟩ : ∃ b : E, Algebra.trace ℚ E (A.δ * ((A.hd n i : 𝓞 E) : E) * (x i : E) * b) ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hw ((traceForm_nondegenerate ℚ E).1 _ fun b => by simpa [Algebra.traceForm_apply] using hall b)
  obtain ⟨m, hm, hy⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic b))
  obtain ⟨c, hc⟩ : ∃ c : 𝓞 E, (c : E) = (m : ℚ) • b := by
    refine ⟨⟨m • b, hy⟩, ?_⟩
    show m • b = (m : ℚ) • b
    rw [zsmul_eq_mul, Algebra.smul_def]
    simp
  have h3 := hint c
  rw [hc, mul_smul_comm, map_smul, smul_eq_mul] at h3
  rcases mul_eq_zero.1 h3 with h5 | h5
  · exact hm (by exact_mod_cast h5)
  · exact hb h5

theorem UpperTheory.Gal.W2.Seed.pFormOKSt :
    FormOKSt := by
  intro E _ _ _ A n
  refine ⟨alternatingMap_sub_base_eq_alternating_sum_removeNth A n, laurent_adjoin_eq_of_image_eq A n, fun b x y => ?_⟩
  rw [Arith.EF_apply, Arith.EF_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, A.bar_bar]
  ring
end
