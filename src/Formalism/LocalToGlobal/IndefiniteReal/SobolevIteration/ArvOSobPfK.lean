module

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsMInfNhd
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.GlobalThetaOrthogonality

@[expose] public section

noncomputable section

open Formalism.IndefR.Datum Matrix
open scoped ComplexOrder

namespace Formalism.IndefR.Tow.SobPf

variable {n : ℕ}

theorem quad_smul (A : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) (x : Fin n → ℂ) :
    (star ((r : ℂ) • x) ⬝ᵥ A *ᵥ ((r : ℂ) • x)) = (r : ℂ) ^ 2 * (star x ⬝ᵥ A *ᵥ x) := by

  have h1 : star ((r : ℂ) • x) = (r : ℂ) • star x := by
    rw [star_smul]; simp
  rw [h1, Matrix.mulVec_smul]
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem continuous_quad (A : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun x : Fin n → ℂ => (star x ⬝ᵥ A *ᵥ x).re := by
  have h : Continuous fun x : Fin n → ℂ => star x ⬝ᵥ A *ᵥ x := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
    fun_prop
  exact Complex.continuous_re.comp h

theorem posDef_lower (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) :
    ∃ c > (0 : ℝ), ∀ x : Fin n → ℂ, c * ‖x‖ ^ 2 ≤ (star x ⬝ᵥ A *ᵥ x).re := by
  apply +allowSynthFailures _root_.ReciprocityTheory.ChartRestriction.DS.S7.IdB.quad_lower <;> assumption

theorem KAt_pres {G s k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ KAt G s) : kᴴ * (G * s) * k = G * s := by

  have hk' : k ∈ Formalism.QuantumDeterminants.UH G ∧ k * s = s * k := hk
  have h1 : kᴴ * G * k = G := hk'.1
  calc kᴴ * (G * s) * k = kᴴ * G * (s * k) := by simp only [Matrix.mul_assoc]
    _ = kᴴ * G * (k * s) := by rw [hk'.2]
    _ = (kᴴ * G * k) * s := by simp only [Matrix.mul_assoc]
    _ = G * s := by rw [h1]

theorem isClosed_KAt (G s : Matrix (Fin n) (Fin n) ℂ) : IsClosed (KAt G s) := by

  have e : KAt G s = {g | gᴴ * G * g = G} ∩ {g | g * s = s * g} := Set.ext fun _ => Iff.rfl
  rw [e]
  refine IsClosed.inter (isClosed_eq ?_ continuous_const) (isClosed_eq ?_ ?_)
  · exact (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
  · exact continuous_id.matrix_mul continuous_const
  · exact continuous_const.matrix_mul continuous_id

theorem isCompact_KAt {G s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) : IsCompact (KAt G s) := by
  obtain ⟨-, -, hP⟩ := hs
  obtain ⟨c, hc, hcP⟩ := posDef_lower (G * s) hP
  have hvec : ∀ k ∈ KAt G s, ∀ x : Fin n → ℂ,
      ‖k *ᵥ x‖ ^ 2 ≤ (star x ⬝ᵥ (G * s) *ᵥ x).re / c := by
    intro k hk x
    have hpres : kᴴ * ((G * s) * k) = G * s := by
      rw [← Matrix.mul_assoc]; exact KAt_pres hk
    have h2 : star (k *ᵥ x) ⬝ᵥ (G * s) *ᵥ (k *ᵥ x) = star x ⬝ᵥ (G * s) *ᵥ x := by
      rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
        hpres, ← Matrix.dotProduct_mulVec]
    have h1 := hcP (k *ᵥ x)
    rw [h2] at h1
    rw [le_div_iff₀ hc, mul_comm]
    exact h1
  refine IsCompact.of_isClosed_subset (isCompact_univ_pi fun i => isCompact_univ_pi fun j =>
    isCompact_closedBall (0 : ℂ)
      (Real.sqrt ((star (Pi.single j 1 : Fin n → ℂ) ⬝ᵥ (G * s) *ᵥ (Pi.single j 1 : Fin n → ℂ)).re / c)))
    (isClosed_KAt G s) ?_
  intro k hk
  refine Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => ?_
  rw [mem_closedBall_zero_iff]
  have hcomp : (k *ᵥ (Pi.single j 1 : Fin n → ℂ)) i = k i j := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hle : ‖k i j‖ ≤ ‖k *ᵥ (Pi.single j 1 : Fin n → ℂ)‖ := by
    rw [← hcomp]; exact norm_le_pi_norm _ i
  have hsq : ‖k i j‖ ^ 2 ≤ (star (Pi.single j 1 : Fin n → ℂ) ⬝ᵥ (G * s) *ᵥ (Pi.single j 1 : Fin n → ℂ)).re / c :=
    le_trans (pow_le_pow_left₀ (norm_nonneg _) hle 2) (hvec k hk _)
  calc ‖k i j‖ = |‖k i j‖| := (abs_norm _).symm
    _ ≤ _ := Real.abs_le_sqrt hsq

end Formalism.IndefR.Tow.SobPf

end
