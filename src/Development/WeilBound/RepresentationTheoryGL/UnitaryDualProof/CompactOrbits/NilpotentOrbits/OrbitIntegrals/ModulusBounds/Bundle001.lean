module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.DetEqOfSurj
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ZNClosed
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.EntIntegral
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

noncomputable section

set_option linter.unusedSectionVars false

open Matrix Module ValuativeRel MeasureTheory GroundTheory.Automorphic.GLnLocal

namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem conj_sub_one (g u : GL (Fin n) k) : (g⁻¹ * u * g).val - 1 = g⁻¹.val * (u.val - 1) * g.val := by
  simp only [Units.val_mul, mul_sub, sub_mul, mul_one, Units.inv_mul]

theorem mem_stab_iff (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (c : Matrix (Fin n) (Fin n) k)
    (p : Sp k n) (u : GL (Fin n) k) (hcu : u.val * c = c * u.val) (hu : u.val - 1 ∈ Bz Z) :
    u ∈ stab Z p ↔ u.val - 1 ∈ cS Z (p.1 - c) p.2 := by
  have e : (u.val - 1) * (p.1 - c) - (p.1 - c) * (u.val - 1) =
      (u.val * p.1 - p.1 * u.val) - (u.val * c - c * u.val) := by noncomm_ring
  rw [hcu, sub_self, sub_zero] at e
  have e1 : (u.val - 1) * (p.1 - c) = (p.1 - c) * (u.val - 1) ↔ u.val * p.1 = p.1 * u.val := by
    rw [← sub_eq_zero, e, sub_eq_zero]
  have e2 : u.val * p.1 * u⁻¹.val = p.1 ↔ u.val * p.1 = p.1 * u.val := by
    constructor
    · intro h
      calc u.val * p.1 = u.val * p.1 * u⁻¹.val * u.val := by simp [mul_assoc]
        _ = p.1 * u.val := by rw [h]
    · intro h
      rw [h, mul_assoc, Units.mul_inv, mul_one]
  have e3 : u.val *ᵥ p.2 = p.2 ↔ (u.val - 1) *ᵥ p.2 = 0 := by
    rw [sub_mulVec, one_mulVec, sub_eq_zero]
  show (u ∈ Gz Z ∧ act u p = p) ↔ _
  rw [mem_Gz_iff]
  simp only [act, Prod.ext_iff]
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨⟨hu, e1.2 (e2.1 h1)⟩, e3.1 h2⟩
  · rintro ⟨⟨-, h1⟩, h2⟩
    exact ⟨hu, e2.2 (e1.1 h1), e3.2 h2⟩

end PositivityTheory.RgUd.T.Nil.Orb.BModbound
end
end

section

noncomputable section

set_option linter.unusedSectionVars false

open Matrix Module ValuativeRel MeasureTheory GroundTheory.Automorphic.GLnLocal

namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def RatioP (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) : Prop :=
  ∀ (V : Submodule k (Matrix (Fin n) (Fin n) k)) (γ : ValueGroupWithZero k), γ ≠ 0 →
    ∀ (φ : V ≃ₗ[k] V) (X Y : AddSubgroup (Matrix (Fin n) (Fin n) k)),
    (∀ y, y ∈ X ↔ y ∈ V ∧ ∀ i j, valuation k (y i j) ≤ γ) →
    (∀ y, y ∈ Y ↔ ∃ x : V, (x : Matrix (Fin n) (Fin n) k) ∈ X ∧ ((φ x : V) : Matrix (Fin n) (Fin n) k) = y) →
    (X ⊓ Y).relIndex X ≠ 0 ∧ (X ⊓ Y).relIndex Y ≠ 0 ∧
      ((X ⊓ Y).relIndex Y : ℝ) / ((X ⊓ Y).relIndex X : ℝ) = (distribHaarChar k (LinearEquiv.det φ) : ℝ)

theorem adL_restrict_inj (g : GL (Fin n) k) (W : Submodule k (Matrix (Fin n) (Fin n) k))
    (hW : ∀ a ∈ W, adL g a ∈ W) : Function.Injective ((adL g).restrict hW) := by
  intro a b hab
  apply Subtype.ext
  have h := congrArg (fun z : W => g⁻¹.val * (z : Matrix (Fin n) (Fin n) k) * g.val) hab
  simp only [LinearMap.coe_restrict_apply, adL_apply, adL_inv_adL] at h
  exact h

theorem mem_cj_iff_exists (g : GL (Fin n) k) (W : Submodule k (Matrix (Fin n) (Fin n) k))
    (hW : ∀ a ∈ W, adL g a ∈ W) (γ : ValueGroupWithZero k) (y : Matrix (Fin n) (Fin n) k) :
    y ∈ cj g (lat W γ) ↔ ∃ z : W, (z : Matrix (Fin n) (Fin n) k) ∈ lat W γ ∧
      ((LinearEquiv.ofInjectiveEndo _ (adL_restrict_inj g W hW) z : W) : Matrix (Fin n) (Fin n) k) = y := by
  rw [mem_cj]
  constructor
  · intro h
    refine ⟨⟨_, (mem_lat.1 h).1⟩, h, ?_⟩
    rw [LinearEquiv.coe_ofInjectiveEndo, LinearMap.coe_restrict_apply, adL_apply, adL_adL_inv]
  · rintro ⟨z, hz, rfl⟩
    rw [LinearEquiv.coe_ofInjectiveEndo, LinearMap.coe_restrict_apply, adL_apply, adL_inv_adL]
    exact hz

theorem det_ofInjectiveEndo (g : GL (Fin n) k) (W : Submodule k (Matrix (Fin n) (Fin n) k))
    (hW : ∀ a ∈ W, adL g a ∈ W) :
    ((LinearEquiv.det (LinearEquiv.ofInjectiveEndo _ (adL_restrict_inj g W hW)) : kˣ) : k) =
      LinearMap.det ((adL g).restrict hW) := by
  rw [LinearEquiv.coe_det]
  congr 1

theorem comm_of_mem_cS (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x : Matrix (Fin n) (Fin n) k)
    (v : Fin n → k) (u : GL (Fin n) k) (h : u.val - 1 ∈ cS Z x v) : u.val * x = x * u.val := by
  have h2 := h.1.2
  rw [sub_mul, mul_sub, one_mul, mul_one] at h2
  exact sub_left_inj.1 h2

end PositivityTheory.RgUd.T.Nil.Orb.BModbound
end
end
