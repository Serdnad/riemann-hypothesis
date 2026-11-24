module

import all Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrSmooth
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.LocSec
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

@[expose] public section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr
open scoped TensorProduct ContDiff Topology

namespace UpperTheory.V.Lit.Geo.Cs

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

private theorem inv_smooth {τ : X → GL (Fin a) (Cinf E)} {x : X}
    (h : ContDiffAt ℝ ∞ (fun y => toL (τ y).val) x) (i j : Fin a) :
    ContDiffAt ℝ ∞ (fun y => (τ y)⁻¹.val i j) x := by
  apply _root_.UpperTheory.V.Lit.Dr.inv_smooth <;> assumption

private theorem sand_smooth {σ : X → GL (Fin a) (Cinf E)} {x : X}
    (h : ∀ i j, ContDiffAt ℝ ∞ (fun y => (σ y).val i j) x) (v : HV E a) :
    ContDiffAt ℝ ∞ (fun y => sand (σ y) v) x := by
  apply _root_.UpperTheory.V.Lit.Dr.sand_smooth <;> assumption

private theorem clm_smooth {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {f : X → V →L[ℝ] V} {x : X} (h : ∀ v, ContDiffAt ℝ ∞ (fun y => f y v) x) : ContDiffAt ℝ ∞ f x := by
  let e₁ : V ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ) := .ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  let e₂ := (e₁.arrowCongr (1 : V ≃L[ℝ] V)).trans (ContinuousLinearEquiv.piRing (Fin (Module.finrank ℝ V)))
  have e : f = fun y => e₂.symm (e₂ (f y)) := funext fun y => (e₂.symm_apply_apply _).symm
  rw [e]
  exact e₂.symm.contDiff.contDiffAt.comp x (contDiffAt_pi.2 fun i => h _)

end UpperTheory.V.Lit.Geo.Cs

open UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.secOne :
    SecOne := by
  intro E _ _ a
  obtain ⟨σ, hσ, hs⟩ := locSec E a (hOne E a) hOne_mem_cone
  set k := σ (hOne E a) with hk
  have hk1 : sand k⁻¹ (hOne E a) = hOne E a := by
    have h0 : sand k (hOne E a) = hOne E a := hs.self_of_nhds
    conv_lhs => rw [← h0]
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  have h1 : ∀ i j, ContDiffAt ℝ ∞ (fun p => (σ p * k⁻¹).val i j) (hOne E a) := fun i j => by
    simp only [Units.val_mul, Matrix.mul_apply]
    exact ContDiffAt.sum fun l _ => (contDiffAt_pi.1 (contDiffAt_pi.1 hσ i) l).mul contDiffAt_const
  have h2 : ContDiffAt ℝ ∞ (fun p => toL (σ p * k⁻¹).val) (hOne E a) :=
    contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => h1 i j
  have h3 := inv_smooth (τ := fun p => σ p * k⁻¹) h2
  refine ⟨fun p => σ p * k⁻¹, mul_inv_cancel k, h2,
    contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => h3 i j, ?_, ?_, ?_⟩
  · exact clm_smooth fun v => sand_smooth h1 v
  · exact clm_smooth fun v => sand_smooth (σ := fun p => (σ p * k⁻¹)⁻¹) h3 v
  · filter_upwards [hs] with p hp
    rw [map_mul, ContinuousLinearMap.mul_apply, hk1, hp]
