module

import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvGrp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
public import Formalism.HermitianCurvature.StatementB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
public import Formalism.SharedLemmas.HpkSq

@[expose] public section

open Matrix

noncomputable section

namespace PI.MirrorSection₂

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

section Grp

variable {k r : ℕ}

theorem hpk_sq (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  first
  | exact _root_.Formalism.SharedLemmas.upq_hpk_mul_self
  | (apply _root_.Formalism.SharedLemmas.upq_hpk_mul_self <;> assumption)

theorem uh_inv {a : B.Mat k r} (ha : a ∈ UH (Hpk k r)) :
    a * a⁻¹ = 1 ∧ a⁻¹ * a = 1 ∧ a⁻¹ ∈ UH (Hpk k r) := by
  apply _root_.PI.WBL.Cv.uh_inv <;> assumption

theorem col_eq (g : B.Mat k r) (j : Fin (2 * r + k + 1)) : g *ᵥ bvec j = fun i => g i j := by
  funext i
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

def lowS (k r a : ℕ) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) where
  carrier := {y | ∀ i : Fin (2 * r + k + 1), a ≤ i.val → y i = 0}
  add_mem' := by
    intro x y hx hy i hi
    simp [hx i hi, hy i hi]
  zero_mem' := by
    intro i _
    rfl
  smul_mem' := by
    intro c x hx i hi
    simp [hx i hi]

theorem maps_low {n : B.Mat k r} (hn : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
      n i (eI k r a) = if i = eI k r a then 1 else 0) {a : ℕ} (har : a ≤ r) :
    ∀ y ∈ lowS k r a, n *ᵥ y ∈ lowS k r a := by
  intro y hy i hi
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hl : a ≤ l.val
  · rw [hy l hl, mul_zero]
  · have hlr : l.val < r := by omega
    have hle : (eI k r ⟨l.val, hlr⟩) = l := Fin.ext rfl
    have := hn ⟨l.val, hlr⟩ i (by simp; omega)
    rw [hle] at this
    rw [this, if_neg (by intro h; rw [h] at hi; omega), zero_mul]

theorem onto_low {g : B.Mat k r} (hg : g⁻¹ * g = 1) {a : ℕ} (hmaps : ∀ y ∈ lowS k r a, g *ᵥ y ∈ lowS k r a) :
    ∀ y ∈ lowS k r a, ∃ x ∈ lowS k r a, g *ᵥ x = y := by
  let f : lowS k r a →ₗ[ℂ] lowS k r a := (Matrix.mulVecLin g).restrict hmaps
  have hinj : Function.Injective f := by
    intro x x' hxx
    have h1 : g *ᵥ (x : Fin (2 * r + k + 1) → ℂ) = g *ᵥ x' := congrArg Subtype.val hxx
    have h2 := congrArg (fun v => g⁻¹ *ᵥ v) h1
    simp only [Matrix.mulVec_mulVec, hg, Matrix.one_mulVec] at h2
    exact Subtype.ext h2
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  intro y hy
  obtain ⟨x, hx⟩ := hsurj ⟨y, hy⟩
  exact ⟨x.1, x.2, congrArg Subtype.val hx⟩

theorem n_inv {n : B.Mat k r} (hn : n ∈ Nset k r) : n⁻¹ ∈ Nset k r := by
  apply _root_.Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.n_inv_mem <;> assumption

theorem uw_inv {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z) : h⁻¹ ∈ UWset k r z := by
  have hu := uh_inv hh.1
  have back : ∀ v, h *ᵥ v = v → h⁻¹ *ᵥ v = v := by
    intro v hv
    calc h⁻¹ *ᵥ v = h⁻¹ *ᵥ (h *ᵥ v) := by rw [hv]
      _ = v := by rw [Matrix.mulVec_mulVec, hu.2.1, Matrix.one_mulVec]
  exact ⟨hu.2.2, fun a => ⟨back _ (hh.2.1 a).1, back _ (hh.2.1 a).2⟩, back _ hh.2.2⟩

end Grp

end PI.MirrorSection₂
