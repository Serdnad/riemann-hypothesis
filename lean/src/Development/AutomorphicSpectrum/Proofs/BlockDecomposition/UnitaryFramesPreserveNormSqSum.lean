import Mathlib
open Matrix

namespace GlobalTheory.CompanionTheory.UnitFrame

theorem normSq_eq_scalar_mul_form {m : ℕ} (J : Matrix (Fin m) (Fin m) ℂ) (fr : GL (Fin m) ℂ)
    (ζ : ℂ) (s : ℤˣ)
    (h : ζ • (fr.1ᵀ * J * fr.1.map star) = ((s : ℤ) : ℂ) • 1) (v : Fin m → ℂ) :
    ((∑ a, ‖((fr⁻¹).1 *ᵥ v) a‖ ^ 2 : ℝ) : ℂ) =
      (((s : ℤ) : ℂ) * star ζ) * (star v ⬝ᵥ (J.map star *ᵥ v)) := by
  obtain ⟨w, hw, hv⟩ : ∃ w, (fr⁻¹).1 *ᵥ v = w ∧ v = fr.1 *ᵥ w :=
    ⟨_, rfl, by rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]⟩
  rw [hw]
  subst hv
  have hc : ((s : ℤ) : ℂ) * ((s : ℤ) : ℂ) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hB : star ζ • (fr.1ᵀ * J * fr.1.map star).map star =
      ((s : ℤ) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) := by
    ext i j
    have h1 := congrArg star (congrFun (congrFun h i) j)
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul'] at h1 ⊢
    rw [h1]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hX : (fr.1ᵀ * J * fr.1.map star).map star = fr.1ᴴ * J.map star * fr.1 := by
    ext i j
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
      star_sum, star_mul', star_star]
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, ← hX, mul_assoc,
    ← smul_eq_mul (star ζ), ← dotProduct_smul, ← smul_mulVec, hB, smul_mulVec, one_mulVec, dotProduct_smul,
    smul_eq_mul, ← mul_assoc, hc, one_mul]
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem normSq_pos {m : ℕ} (hm : 1 ≤ m) (fr : GL (Fin m) ℂ) :
    0 < ∑ a, ‖((fr⁻¹).1 *ᵥ (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ))) a‖ ^ 2 := by
  have hne : (fr⁻¹).1 *ᵥ (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ)) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun u => fr.1 *ᵥ u) h0
    simp only [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec,
      mulVec_zero] at h1
    exact one_ne_zero (Pi.single_eq_zero_iff.mp h1)
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
  exact Finset.sum_pos' (fun i _ => by positivity)
    ⟨a, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr ha) 2⟩

theorem normSq_eq_norm_form_of_unit_frame {m : ℕ} (J : Matrix (Fin m) (Fin m) ℂ)
    (fr : GL (Fin m) ℂ) (ζ : ℂ) (s : ℤˣ) (hζ : ‖ζ‖ = 1)
    (h : ζ • (fr.1ᵀ * J * fr.1.map star) = ((s : ℤ) : ℂ) • 1) (v : Fin m → ℂ) :
    ∑ a, ‖((fr⁻¹).1 *ᵥ v) a‖ ^ 2 = ‖star v ⬝ᵥ (J.map star *ᵥ v)‖ := by
  have hs : ‖((s : ℤ) : ℂ)‖ = 1 := by
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp
  have hsum : 0 ≤ ∑ a, ‖((fr⁻¹).1 *ᵥ v) a‖ ^ 2 :=
    Finset.sum_nonneg fun a _ => sq_nonneg _
  simpa only [Complex.norm_real, Real.norm_of_nonneg hsum, norm_mul, norm_star, hs, hζ, one_mul]
    using congrArg norm (normSq_eq_scalar_mul_form J fr ζ s h v)

theorem normSq_eq_of_unit_frames : ∀ (m : ℕ), 1 ≤ m → ∀ (J : Matrix (Fin m) (Fin m) ℂ) (fr fr' : GL (Fin m) ℂ) (ζ ζ' : ℂ) (s s' : ℤˣ), (ζ = 1 ∨ ζ = Complex.I) → (ζ' = 1 ∨ ζ' = Complex.I) → ζ • (fr.1ᵀ * J * fr.1.map star) = ((s : ℤ) : ℂ) • 1 → ζ' • (fr'.1ᵀ * J * fr'.1.map star) = ((s' : ℤ) : ℂ) • 1 → ∀ v : Fin m → ℂ, ∑ a, ‖((fr⁻¹).1 *ᵥ v) a‖ ^ 2 = ∑ a, ‖((fr'⁻¹).1 *ᵥ v) a‖ ^ 2 := by
  intro m _ J fr fr' ζ ζ' s s' hζ hζ' h h' v
  have norm_eq_one (z : ℂ) (hz : z = 1 ∨ z = Complex.I) : ‖z‖ = 1 := by
    rcases hz with rfl | rfl <;> simp
  exact (normSq_eq_norm_form_of_unit_frame J fr ζ s (norm_eq_one ζ hζ) h v).trans
    (normSq_eq_norm_form_of_unit_frame J fr' ζ' s' (norm_eq_one ζ' hζ') h' v).symm

end GlobalTheory.CompanionTheory.UnitFrame

theorem GlobalTheory.T.unitary_frames_preserve_norm_sq_sum : type_of% @GlobalTheory.CompanionTheory.UnitFrame.normSq_eq_of_unit_frames :=
  @GlobalTheory.CompanionTheory.UnitFrame.normSq_eq_of_unit_frames
