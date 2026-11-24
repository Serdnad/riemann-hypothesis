module

import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IpTheta
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharLem
public import Formalism.LocalToGlobal.IndefiniteReal.PHeisThA
import Mathlib.RingTheory.PiTensorProduct

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Psi

variable {ψ : AddChar (AF D.host.F) ℂ}

theorem psi_norm (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : ‖ψ a‖ = 1 := hψ.1.2.1 a

theorem psi_ne (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : ψ a ≠ 0 := by
  intro h
  have h1 := psi_norm hψ a
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

theorem psi_cont (hψ : IsStdChar D ψ (-1)) : Continuous ψ := hψ.1.1

end Psi

section Cont

variable (S T : HSp D)

theorem cont_trace : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
  IsModuleTopology.continuous_of_linearMap _

def cAlin (D : D7) : AE D →ₗ[AF D.host.F] AE D where
  toFun := cA D
  map_add' := map_add _
  map_smul' := Formalism.IndefR.PHeisTh.cA_smul

theorem cont_cA : Continuous (cA D) :=
  IsModuleTopology.continuous_of_linearMap (cAlin D)

theorem cont_hO : Continuous fun p : MO S T × MO S T => hO S T p.1 p.2 := by
  have hcA : Continuous (cA D) := cont_cA
  delta hO
  fun_prop

theorem cont_symplO : Continuous fun p : MO S T × MO S T => symplO S T p.1 p.2 := by
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := cont_trace
  have hh := cont_hO S T
  delta symplO
  first
    | exact ht.comp (continuous_const.mul hh)

theorem cont_symplO_left (w : MO S T) : Continuous fun z : MO S T => symplO S T z w := by
  have h : Continuous (Function.uncurry (symplO S T)) := cont_symplO S T
  exact h.uncurry_right w

theorem cont_symplOH_left (w : MO S T) : Continuous fun z : MO S T => symplOH S T z w := by
  delta symplOH
  exact continuous_const.mul (cont_symplO_left S T w)

end Cont

section Per

variable (S T : HSp D)

end Per

section Theta

variable {ψ : AddChar (AF D.host.F) ℂ} (S T : HSp D)

theorem cont_heis (hψ : IsStdChar D ψ (-1)) {f : MO S T → ℂ} (hf : IsThetaFunO ψ S T f) (v : MO S T) :
    Continuous (heisO ψ S T v f) := by
  delta heisO
  exact ((psi_cont hψ).comp (cont_symplOH_left S T v)).mul (hf.3.comp (continuous_add_const v))

theorem theta_zero : IsThetaFunO ψ S T 0 := by
  exact ⟨fun γ w => by simp, ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun u _ _ => by funext z; simp [heisO]⟩, continuous_zero,
    fun k L _ _ _ => contDiff_const⟩

theorem theta_add {f g : MO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (f + g) := by
  apply _root_.Formalism.IndefR.Eqv.thetaO_add <;> assumption

theorem theta_smul (c : ℂ) {f : MO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) := by
  apply _root_.GlobalTheory.WeilVacMove.isTheta_smul <;> assumption

end Theta

section Svn

variable {ψ : AddChar (AF D.host.F) ℂ} (S T : HSp D)

end Svn

end Formalism.IndefR.Fin

end
