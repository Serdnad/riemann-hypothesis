module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeSizeContinuity.DetMono
public import Formalism.LocalToGlobal.HermitianForms.TiedSym
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.HformSmulRightB
public import Formalism.LocalToGlobal.HermitianForms.TiedBrUnit
import Mathlib.Analysis.Matrix.PosDef

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix Formalism.UG
open scoped ComplexOrder

theorem exists_on_of_posDef {k : ℕ} (H : Matrix (Fin k) (Fin k) ℂ) (hH : H.PosDef) :
    ∃ o : Matrix (Fin k) (Fin k) ℂ, IsUnit o.det ∧ oᴴ * H * o = 1 := by
  apply +allowSynthFailures _root_.PI.UnitaryGroupMassFormula.HermDefON.exists_congr_one <;> assumption

variable {D : D7}

theorem embT_sig (τ : D.what₂.Tau) (x : D.host.E) : embT D τ (sigD D x) = starRingEnd ℂ (embT D τ x) :=
  D.sp.cm.cmUnram.2.1 (embT D τ) x

theorem map_cT {m n : Type} (M : Matrix m n D.host.E) (τ : D.what₂.Tau) :
    ((M.map (sigD D : D.host.E →+* D.host.E))ᵀ).map (embT D τ) = (M.map (embT D τ))ᴴ := by
  ext i j
  simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, RingHom.coe_coe]
  rw [embT_sig]
  rfl


variable (D) in
theorem gramP_eq : gramP D = ((iXm D).map (sigD D : D.host.E →+* D.host.E))ᵀ * gramN D D.R.m le_rfl * iXm D := by
  ext a b
  rw [gramOf_apply]
  have hc : ∀ i : Fin (D.R.N D.R.m - 1), (fun k => iXm D k i) = iXc D (Pi.single i 1) := by
    intro i; funext k; simp only [iXm, LinearMap.toMatrix'_apply]
  rw [hc, hc, hform_iXc]
  simp [hform, Pi.single_apply]


variable (D) in
theorem iXm_leftInv : ∃ L : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m)) D.host.E, L * iXm D = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (iXc D) (LinearMap.ker_eq_bot.mpr (iXc_injective D))
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [iXm, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

theorem gramP_posDef {Ch : ℕ → Type} {u : D.what₂.Word} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (Tf : FormsTiedSym D u Ch chOf)
    (τ : D.what₂.Tau) : (gramC (gramP D) (embT D) τ).PosDef := by
  obtain ⟨C, hC, -, -⟩ := (Tf.val D.R.m le_rfl (Or.inr rfl)).de
  have hC' : ((C.1.map (sigD D : D.host.E →+* D.host.E))ᵀ * C.1) = gramN D D.R.m le_rfl := hC
  obtain ⟨L, hL⟩ := iXm_leftInv D
  set A : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m - 1)) ℂ := (C.1 * iXm D).map (embT D τ) with hA
  have hG : gramC (gramP D) (embT D) τ = Aᴴ * A := by
    have e1 : ((iXm D).map (sigD D : D.host.E →+* D.host.E))ᵀ * (((C.1).map (sigD D : D.host.E →+* D.host.E))ᵀ * C.1) * iXm D =
        ((C.1 * iXm D).map (sigD D : D.host.E →+* D.host.E))ᵀ * (C.1 * iXm D) := by
      rw [Matrix.map_mul, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    simp only [gramC]
    rw [gramP_eq, ← hC', e1, Matrix.map_mul, map_cT, hA]
  have hinj : Function.Injective A.mulVec := by
    intro x y hxy
    have hCi : IsUnit C.1.det := (Matrix.isUnit_iff_isUnit_det _).mp C.isUnit
    have h1 : ((L * C.1⁻¹) * (C.1 * iXm D)).map (embT D τ) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc C.1⁻¹, Matrix.nonsing_inv_mul _ hCi, Matrix.one_mul, hL,
        Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 := congrArg (fun v => ((L * C.1⁻¹).map (embT D τ)) *ᵥ v) hxy
    simp only [Matrix.mulVec_mulVec, hA, ← Matrix.map_mul, h1, Matrix.one_mulVec] at h2
    exact h2
  rw [hG]
  exact Matrix.PosDef.conjTranspose_mul_self A hinj

theorem exists_onP {Ch : ℕ → Type} {u : D.what₂.Word} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (Tf : FormsTiedSym D u Ch chOf) :
    ∃ o : FrP D, ∀ τ, (o.1 τ)ᴴ * gramC (gramP D) (embT D) τ * o.1 τ = 1 := by
  have h := fun τ => exists_on_of_posDef (k := D.R.N D.R.m - 1) (gramC (gramP D) (embT D) τ) (gramP_posDef Tf τ)
  choose o ho1 ho2 using h
  exact ⟨⟨o, ho1⟩, ho2⟩

end Formalism.L2.GlobalTheoryTheory.Br
