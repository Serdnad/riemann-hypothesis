import Statements
import Development.AutomorphicArithmetic.CharacterBoxes.HalfPlane
import Development.AutomorphicArithmetic.CharacterBoxes.RiemannHypothesisOfEveryCharacter

open Complex

open DirichletCharacter in
theorem Formalism.VW.gammaFactor_ne_zero {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) : gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos hs
  · rw [h.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos (by rw [add_re, one_re]; linarith)

namespace Claim

/-- The reverse triangle inequality bounds an Euler factor for any complex coefficient
and any positive real base. -/
theorem eulerFactor_norm_lower_bound {x : ℝ} (hx : 0 < x) (a s : ℂ) :
    1 - ‖a‖ * x ^ (-s.re) ≤ ‖1 - a * (x : ℂ) ^ (-s)‖ := by
  simpa only [norm_one, norm_mul, norm_cpow_eq_rpow_re_of_pos hx, neg_re] using
    norm_sub_norm_le (1 : ℂ) (a * (x : ℂ) ^ (-s))

theorem factor_ne_zero {M : ℕ} (ψ : DirichletCharacter ℂ M) {s : ℂ} (hs : 0 < s.re) (p : ℕ)
    (hp : p.Prime) : (1 : ℂ) - ψ p * (p : ℂ) ^ (-s) ≠ 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp1
  have hpow := Real.rpow_lt_one_of_one_lt_of_neg hp1 (neg_lt_zero.mpr hs)
  have hmul := (mul_le_of_le_one_left (Real.rpow_nonneg hp0.le _) (ψ.norm_le_one p)).trans_lt hpow
  apply norm_pos_iff.mp
  simpa only [ofReal_natCast] using
    (sub_pos.mpr hmul).trans_le (eulerFactor_norm_lower_bound hp0 (ψ p) s)

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

private theorem primitive_inv {M : ℕ} [NeZero M] {ψ : DirichletCharacter ℂ M}
    (hψ : ψ.IsPrimitive) : ψ⁻¹.IsPrimitive := by
  rwa [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]

/-- Completion makes zero reflection unconditional for a primitive character. -/
theorem completed_zero_iff_reflect {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M)
    (hψ : ψ.IsPrimitive) {s : ℂ} :
    DirichletCharacter.completedLFunction ψ s = 0 ↔
      DirichletCharacter.completedLFunction ψ⁻¹ (1 - s) = 0 := by
  constructor
  · intro hz
    rw [(primitive_inv hψ).completedLFunction_one_sub, inv_inv, hz, mul_zero]
  · intro hz
    rw [← sub_sub_cancel (1 : ℂ) s, hψ.completedLFunction_one_sub, hz, mul_zero]

/-- An ordinary zero reflects whenever the input gamma factor is nonzero and both
completion identities apply. The output gamma factor may vanish. -/
theorem prim_reflect_of_gamma_ne_zero {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M)
    (hψ : ψ.IsPrimitive) {s : ℂ} (h₀ : s ≠ 0 ∨ M ≠ 1) (h₁ : 1 - s ≠ 0 ∨ M ≠ 1)
    (hgamma : DirichletCharacter.gammaFactor ψ s ≠ 0)
    (hz : DirichletCharacter.LFunction ψ s = 0) :
    DirichletCharacter.LFunction ψ⁻¹ (1 - s) = 0 := by
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor ψ s h₀,
    div_eq_zero_iff, or_iff_left hgamma] at hz
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor ψ⁻¹ (1 - s) h₁,
    (completed_zero_iff_reflect ψ hψ).mp hz, zero_div]

theorem prim_reflect {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M) (hψ : ψ.IsPrimitive) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (h : DirichletCharacter.LFunction ψ s = 0) :
    DirichletCharacter.LFunction ψ⁻¹ (1 - s) = 0 :=
  prim_reflect_of_gamma_ne_zero ψ hψ
    (Or.inl fun e => by simp [e] at hs0)
    (Or.inl (sub_ne_zero.mpr fun e => by simp [← e] at hs1))
    (gamma_ne_zero ψ hs0) h

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

/-- Pass to the primitive character, then use the functional equation to bring any
zero left of the critical line into the right half of the strip. -/
theorem strip_of_primitive_right_strip (h : PrimitiveDirichletLNonvanishingInRightStrip) :
    Strip := by
  intro N _ χ s hs0 hs1 hz
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hχ := χ.primitiveCharacter_isPrimitive
  have hzero := prim_zero χ hs0 hs1 hz
  refine le_antisymm (le_of_not_gt fun hright => h _ _ hχ s hright hs1 hzero) ?_
  refine le_of_not_gt fun hleft => ?_
  have hright : 1 / 2 < (1 - s).re := by rw [sub_re, one_re]; linarith
  have h1 : (1 - s).re < 1 := by rw [sub_re, one_re]; linarith
  exact h _ _ (primitive_inv hχ) (1 - s) hright h1 (prim_reflect _ hχ hs0 hs1 hzero)

theorem strip (h : HalfPlane) : Strip :=
  strip_of_primitive_right_strip (halfPlane_iff_primitive_right_strip.mp h)

theorem primitive_strip (h : Strip) : PrimitiveDirichletLZerosOnLine :=
  fun N _ χ _ => h N χ

theorem primitive_strip_iff_primitive_right_strip :
    PrimitiveDirichletLZerosOnLine ↔ PrimitiveDirichletLNonvanishingInRightStrip := by
  refine ⟨?_, fun h => primitive_strip (strip_of_primitive_right_strip h)⟩
  intro h N _ χ hχ s hright hs1 hz
  have hs0 : 0 < s.re := (by norm_num : (0 : ℝ) < 1 / 2).trans hright
  exact hright.ne' (h N χ hχ s hs0 hs1 hz)

theorem strip_iff_primitive_strip : Strip ↔ PrimitiveDirichletLZerosOnLine :=
  ⟨primitive_strip, fun h => strip_of_primitive_right_strip
    (primitive_strip_iff_primitive_right_strip.mp h)⟩

theorem halfPlane_iff_strip : HalfPlane ↔ Strip :=
  ⟨strip, fun h => halfPlane_iff_primitive_right_strip.mpr
    (primitive_strip_iff_primitive_right_strip.mp (primitive_strip h))⟩

theorem zeta (h : HalfPlane) : Zeta :=
  UpperTheory.riemannHypothesis_of_everyCharacter h

theorem zeta_iff : Zeta ↔ RiemannHypothesis := Iff.rfl

end Claim
