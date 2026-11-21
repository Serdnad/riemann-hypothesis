import Formalism.SizeWindowBrackets.PowerBoundGivesRiemannHypothesis
import Formalism.GammaFactorNonvanishing.RhOfRight
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.Window
import Development.AutomorphicArithmetic.PrimitiveCosets.GzEq
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ZeroFreeOfRpowWindow

noncomputable section

namespace Formalism.LFunctionChainParameters.ConditionalMainTheorem

open Formalism.HC

private def zetaFamily : Deduction.CharFamily where
  ι := Unit
  fin := inferInstance
  N := fun _ => 1
  nz := fun _ => inferInstance
  χ := fun _ => 1
  a := fun _ => 1
  a_pos := fun _ => zero_lt_one
  adm := fun _ => Or.inl rfl

private theorem zetaFamily_gm (y : ℝ) : Deduction.Gm zetaFamily y = Gz y := by
  have hχ : (fun n : ℕ => (1 : DirichletCharacter ℂ 1) (n : ZMod 1)) = fun _ => 1 := by
    funext n
    rw [Subsingleton.elim (n : ZMod 1) 1]
    simp
  have h := UpperTheory.Comparison₂.Gz_eq y
  rw [h.1, h.2]
  change (∑ _ : Unit, 1 * (Deduction.Gchi (1 : DirichletCharacter ℂ 1) y).re) = Deduction.G y
  rw [Fintype.sum_unique, one_mul, Deduction.Gchi, if_pos rfl, hχ]
  simp only [Deduction.G, Complex.sub_re, Complex.add_re, Complex.ofReal_re]

/-- A one-sided bound on the centered zeta sum in arbitrarily large windows gives nonvanishing. -/
theorem zeta_ne_zero_of_window_bound {θ la : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1)
    (hla : 1 < la) (hG : HasWindows {y | Gz y ≤ y ^ θ} la) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 := by
  have hz := Deduction.zeroFree_of_rpow_window zetaFamily (δ := la - 1) (C := 1)
    hθ hθ₁ (sub_pos.mpr hla) (fun Y₀ => by
      obtain ⟨Y, hY, hWin⟩ := hG Y₀
      refine ⟨Y, hY, fun y hy => ?_⟩
      rw [show (1 : ℝ) + (la - 1) = la by ring] at hy
      rw [zetaFamily_gm, one_mul]
      exact hWin y hy.1 hy.2)
  intro s hs
  have h := hz () s hs
  change DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s ≠ 0 at h
  simpa only [DirichletCharacter.LFunction_modOne_eq] using h

theorem landau_zero_free_half_plane : LandauZeroFreeHalfPlane := by
  intro θ hθ hθ₁ y₀ h
  exact zeta_ne_zero_of_window_bound hθ hθ₁ (la := 2) (by norm_num)
    (hasWindows_of_large (S := {y | Gz y ≤ y ^ θ}) (x0 := y₀) h 2)

theorem riemann_hypothesis_of_power_bound : PowerBoundGivesRiemannHypothesis := by
  intro C ε₁ hε₁ growth
  apply VW.rh_of_right
  intro s hs _
  obtain ⟨θ, hθ, hθ'⟩ := exists_between (lt_min (show (1 : ℝ) / 2 < 1 by norm_num) hs)
  have hpos : 0 < |C| + 1 := by positivity
  let ε := min (ε₁ / 2) ((θ - 1 / 2) / (|C| + 1))
  have hε : 0 < ε := lt_min (half_pos hε₁) (div_pos (sub_pos.mpr hθ) hpos)
  have hε₁' : ε < ε₁ := (min_le_left _ _).trans_lt (half_lt_self hε₁)
  have hbudget : C * ε ≤ θ - 1 / 2 := by
    calc
      C * ε ≤ (|C| + 1) * ε := mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) hε.le
      _ = ε * (|C| + 1) := mul_comm _ _
      _ ≤ θ - 1 / 2 := (le_div_iff₀ hpos).mp (min_le_right _ _)
  obtain ⟨x₀, hG⟩ := growth ε hε hε₁'
  refine landau_zero_free_half_plane θ (by linarith) (hθ'.trans_le (min_le_left _ _))
    (max x₀ 1) (fun y hy => ?_) s (hθ'.trans_le (min_le_right _ _))
  exact (hG y (le_of_max_le_left hy)).trans
    (Real.rpow_le_rpow_of_exponent_le (le_of_max_le_right hy) (by linarith))

end Formalism.LFunctionChainParameters.ConditionalMainTheorem

end
