import Development.AutomorphicArithmetic.CharacterBoxes.HalfPlane
import Development.AutomorphicArithmetic.CharacterBoxes.RiemannHypothesisOfEveryCharacter

open Complex

open DirichletCharacter in
theorem Formalism.VW.gammaFactor_ne_zero {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) : gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos hs
  · rw [h.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos (by rw [add_re, one_re]; linarith)

namespace Claim

theorem factor_ne_zero {M : ℕ} (ψ : DirichletCharacter ℂ M) {s : ℂ} (hs : 0 < s.re) (p : ℕ)
    (hp : p.Prime) : (1 : ℂ) - ψ p * (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : ψ p * (p : ℂ) ^ (-s) = 1 := by linear_combination -h
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpow : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hn : ‖ψ p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    calc ‖ψ p‖ * ‖(p : ℂ) ^ (-s)‖ ≤ 1 * ‖(p : ℂ) ^ (-s)‖ := by
          gcongr; exact ψ.norm_le_one _
      _ < 1 := by rw [one_mul]; exact hpow
  rw [h1, norm_one] at hn
  exact lt_irrefl _ hn

theorem nonzero_iff_primitive {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    [NeZero χ.conductor] {s : ℂ} (hs : 0 < s.re) (hχs : χ ≠ 1 ∨ s ≠ 1) :
    DirichletCharacter.LFunction χ s ≠ 0 ↔
      DirichletCharacter.LFunction χ.primitiveCharacter s ≠ 0 := by
  have hprim : χ.primitiveCharacter ≠ 1 ∨ s ≠ 1 := hχs.imp (fun hχ h1 => hχ (by
    rw [← χ.changeLevel_primitiveCharacter, h1, DirichletCharacter.changeLevel_one])) id
  have hL := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level
    χ.primitiveCharacter hprim
  rw [χ.changeLevel_primitiveCharacter] at hL
  rw [hL]
  exact mul_ne_zero_iff_right (Finset.prod_ne_zero_iff.mpr fun p hp =>
    factor_ne_zero _ hs p (Nat.prime_of_mem_primeFactors hp))

theorem prim_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) [NeZero χ.conductor]
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (h : DirichletCharacter.LFunction χ s = 0) :
    DirichletCharacter.LFunction χ.primitiveCharacter s = 0 := by
  have hs : s ≠ 1 := fun e => by rw [e, Complex.one_re] at hs1; exact lt_irrefl _ hs1
  by_contra hprim
  exact ((nonzero_iff_primitive χ hs0 (Or.inr hs)).2 hprim) h

theorem gamma_ne_zero {M : ℕ} [NeZero M] (φ : DirichletCharacter ℂ M) {t : ℂ} (ht : 0 < t.re) :
    DirichletCharacter.gammaFactor φ t ≠ 0 :=
  Formalism.VW.gammaFactor_ne_zero φ ht

theorem prim_reflect {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M) (hψ : ψ.IsPrimitive) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (h : DirichletCharacter.LFunction ψ s = 0) :
    DirichletCharacter.LFunction ψ⁻¹ (1 - s) = 0 := by
  have hs0' : s ≠ 0 := fun e => by simp [e] at hs0
  have hs1' : s ≠ 1 := fun e => by simp [e] at hs1
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor ψ s (Or.inl hs0'),
    div_eq_zero_iff] at h
  have hc := h.resolve_right (gamma_ne_zero ψ hs0)
  have hinv : ψ⁻¹.IsPrimitive := by
    rwa [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor _ _
      (Or.inl (sub_ne_zero.mpr hs1'.symm)),
    hinv.completedLFunction_one_sub, inv_inv, hc, mul_zero, zero_div]

theorem strip (h : HalfPlane) : Strip := by
  unfold HalfPlane at h
  intro N _ χ s hs0 hs1 hz
  have hs : s ≠ 1 := fun e => by rw [e, Complex.one_re] at hs1; exact lt_irrefl _ hs1
  have hs0' : s ≠ 0 := fun e => by rw [e, Complex.zero_re] at hs0; exact lt_irrefl _ hs0
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · exfalso
    have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hp := prim_zero χ hs0 hs1 hz
    have hr := prim_reflect χ.primitiveCharacter χ.primitiveCharacter_isPrimitive hs0 hs1 hp
    have ht : (1 : ℂ) - s ≠ 1 := fun e => hs0' (sub_eq_self.mp e)
    exact h χ.conductor χ.primitiveCharacter⁻¹ (1 - s)
      (by rw [Complex.sub_re, Complex.one_re]; linarith) (Or.inr ht) hr
  · exact heq
  · exact absurd hz (h N χ s hgt (Or.inr hs))

/-- It suffices to establish nonvanishing for primitive characters in the right half of
the open critical strip. Mathlib handles the closed half-plane at and to the right of 1. -/
theorem halfPlane_iff_primitive_right_strip :
    HalfPlane ↔ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s ≠ 0 := by
  constructor
  · intro h N _ χ _ s hhalf h1
    have hs : s ≠ 1 := fun e => by simp [e] at h1
    exact h N χ s hhalf (Or.inr hs)
  · intro h N _ χ s hhalf hχs
    by_cases h1 : s.re < 1
    · intro hz
      have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
      exact h χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive s hhalf h1
        (prim_zero χ (by linarith) h1 hz)
    · exact χ.LFunction_ne_zero_of_one_le_re hχs (le_of_not_gt h1)

theorem zeta (h : HalfPlane) : Zeta :=
  UpperTheory.riemannHypothesis_of_everyCharacter h

theorem zeta_iff : Zeta ↔ RiemannHypothesis := Iff.rfl

end Claim
