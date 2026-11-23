module

import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle004
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct ContDiff ENNReal

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Basic

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem thetaO_add {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (f + g) := by
  apply Formalism.IndefR.Fock.CCR.theta_add <;> assumption

theorem thetaO_smul {f : WO S T → ℂ} (c : ℂ) (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) := by

  obtain ⟨U1, hU1, h1⟩ := hf.level
  constructor
  · intro γ w
    simp only [Pi.smul_apply, smul_eq_mul, hf.quasi]
    ring
  · refine ⟨U1, hU1, fun u hu hfin => ?_⟩
    funext x
    have e1x := congrFun (h1 u hu hfin) x
    simp only [heisO, Pi.smul_apply, smul_eq_mul] at e1x ⊢
    rw [mul_left_comm, e1x]
  · exact hf.cont.const_smul c
  · intro k L hL hfin w
    exact (hf.smooth k L hL hfin w).const_smul c

end Basic

section L2

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

end L2

section Unit

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

end Unit

section Cont

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

end Cont

end Formalism.IndefR.Eqv

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D}

theorem eInf_mul_eFin : eInf D * eFin D = 0 := by
  simp only [eInf, eFin, pairA]
  first
  | exact Prod.ext (mul_zero _) (zero_mul _)
  | (refine Prod.ext ?_ ?_ <;> simp)

theorem eInf_add_eFin : eInf D + eFin D = 1 := by
  simp only [eInf, eFin, pairA]
  first
  | exact Prod.ext (add_zero _) (zero_add _)
  | (refine Prod.ext ?_ ?_ <;> simp)

theorem cA_smul (c : AF D.host.F) (z : AE D) : cA D (c • z) = c • cA D z := by

  unfold cA sigR
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul]
  | add x y hx hy =>
    rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem hO_smul_right (c : AF D.host.F) (x y : WO S T) : hO S T x (c • y) = c • hO S T x y := by

  simp only [hO, Finset.smul_sum, Matrix.smul_apply, Pi.smul_apply, cA_smul, mul_smul_comm, smul_mul_assoc]

theorem hO_smul_left (c : AF D.host.F) (x y : WO S T) : hO S T (c • x) y = c • hO S T x y := by

  simp only [hO, Finset.smul_sum, Matrix.smul_apply, Pi.smul_apply, mul_smul_comm, smul_mul_assoc]

theorem symplOH_smul_right (c : AF D.host.F) (x y : WO S T) : symplOH S T x (c • y) = c * symplOH S T x y := by

  simp only [symplOH, symplO, hO_smul_right, mul_smul_comm, map_smul, smul_eq_mul]
  ring

theorem symplOH_smul_left (c : AF D.host.F) (x y : WO S T) : symplOH S T (c • x) y = c * symplOH S T x y := by

  simp only [symplOH, symplO, hO_smul_left, mul_smul_comm, map_smul, smul_eq_mul]
  ring

theorem symplOH_real_fin (y u : WO S T) (hy : eInf D • y = y) (hu : eFin D • u = u) : symplOH S T y u = 0 := by

  rw [← hy, ← hu, symplOH_smul_left, symplOH_smul_right, ← mul_assoc, eInf_mul_eFin, zero_mul]

theorem wo_real_iff (w : WO S T) : w.map (finPart D) = 0 ↔ eInf D • w = w := by
  constructor
  · intro h
    ext i j
    exact (finPart_eq_zero_iff_smul (w i j)).mp (congrFun (congrFun h i) j)
  · intro h
    ext i j
    exact (finPart_eq_zero_iff_smul (w i j)).mpr (congrFun (congrFun h i) j)

theorem wo_fin_iff (w : WO S T) : w.map (infPart D) = 0 ↔ eFin D • w = w := by
  constructor
  · intro h
    ext i j
    exact (infPart_eq_zero_iff_smul (w i j)).mp (congrFun (congrFun h i) j)
  · intro h
    ext i j
    exact (infPart_eq_zero_iff_smul (w i j)).mpr (congrFun (congrFun h i) j)

end Formalism.IndefR.Eqv

end
end

section

noncomputable section

open MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

def RightInv : Prop :=
  ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (Γ : Subgroup H) [Countable Γ]
    (ν : Measure H) [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant] (𝓕 : Set H),
    IsFundamentalDomain Γ 𝓕 ν → ∀ ψ : H → ℂ, (∀ γ ∈ Γ, ∀ h, ψ (γ * h) = ψ h) → ∀ k : H,
      (IntegrableOn (fun h => ψ (h * k)) 𝓕 ν ↔ IntegrableOn ψ 𝓕 ν) ∧
        ∫ h in 𝓕, ψ (h * k) ∂ν = ∫ h in 𝓕, ψ h ∂ν

section GA

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def UnimodGA (V : HSp D) : Prop :=
  ∀ μ : Measure (GA D V), μ.IsHaarMeasure → μ.IsMulRightInvariant

end GA

section Mult

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def IoUniqueAt : Prop :=
  ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : Mult.DSModel V S)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (Kf : ∀ τ, Submodule ℂ (M.sm τ)) (Sinf Ds : Type) [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup Ds]
    [Module ℂ Ds] (T : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] (⨂[ℂ] τ, M.sm τ)),
    (∀ τ (ℓ : M.H τ →ₗ[ℂ] ℂ), Sobolev₂ (lieAt V τ) (M.rep τ) ℓ → (∀ w ∈ Kf τ, ℓ (w : M.H τ) = 0) →
      ∀ w : M.sm τ, ℓ (w : M.H τ) = 0) →
    (∀ v : ∀ τ, M.sm τ, (∀ τ, v τ ∈ Kf τ) →
      PiTensorProduct.tprod ℂ v ∈ Submodule.span ℂ {x | ∃ φ w, T φ w = x}) →
    ∀ u ∈ Mult.MultT θ M J χ, (∀ φ w, u (T φ w) = 0) → u = 0

end Mult

end Formalism.IndefR.Eqv

end
end
