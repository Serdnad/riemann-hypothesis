module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle070
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle069
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.OmgEquivariant
public import Formalism.HermitianCurvature.Bundle009
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle074
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HighestWeightPolynomials
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
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle157
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted

@[expose] public section

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.OmegaBiInv

theorem omg_N_mul_N : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)), inWb k r z → inWb k r z' → ∀ g ∈ B.GV k r, ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r, GlobalTheory.WigSh.omg k r z z' (n * g * n') = GlobalTheory.WigSh.omg k r z z' (g) := by
  intro k r z z' hz hz' g hg n hn n' hn'
  rw [Matrix.mul_assoc, GlobalTheory.WigSh.OmLeftN.omg_mul_left k r z z' (g * n') n hz hn]
  exact GlobalTheory.WigSh.omg_mul_N k r z z' g n' hz hz' hg hn'

end GlobalTheory.CompanionTheory.OmegaBiInv
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.OmgUW

lemma one_mem_UWset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UWset k r z := by
  simp [UWset, UH]

theorem omg_left_right : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → ∀ g ∈ B.GV k r, (∀ h ∈ UWset k r z, GlobalTheory.WigSh.omg k r z z' (h * g) = GlobalTheory.WigSh.omg k r z z' (g)) ∧ ∀ h' ∈ UWset k r z', GlobalTheory.WigSh.omg k r z z' (g * h') = h'⁻¹ *ᵥ GlobalTheory.WigSh.omg k r z z' (g) := by
  intro k r z z' hz hTz hz' hTz' g hg
  refine ⟨fun h hh => ?_, fun h' hh' => ?_⟩
  · have hhU : h ∈ UH (Hpk k r) := by
      simp only [UWset, Set.mem_setOf_eq] at hh
      exact hh.1
    have hii : h⁻¹⁻¹ = h :=
      Matrix.nonsing_inv_nonsing_inv h
        (Matrix.isUnit_det_of_right_inverse (GlobalTheory.WigSh.OmgEquiv.mul_inv hhU))
    have e := GlobalTheory.WigSh.omg_equivariant k r z z' g h⁻¹ 1 hz hTz hz' hTz' hg
      (GlobalTheory.WigSh.OmgEquiv.inv_mem hh) (one_mem_UWset k r z')
    rw [hii, mul_one, inv_one, Matrix.one_mulVec] at e
    exact e
  · have e := GlobalTheory.WigSh.omg_equivariant k r z z' g 1 h' hz hTz hz' hTz' hg
      (one_mem_UWset k r z) hh'
    rw [inv_one, one_mul] at e
    exact e

end GlobalTheory.CompanionTheory.OmgUW
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.GapLie

theorem capelli_params_diff_int : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (m : Fin n → ℂ), GlRel E → (∀ w v, qdet E w v = Qr.cpol m w • v) → ∀ i j, ∃ N : ℤ, m i - m j = (N : ℂ) := by
  intro V _ _ _ _ n E m hE hq
  obtain ⟨ν, v, -, hv0, hw, -⟩ := Formalism.FourierDecayAlt.P.exists_singular_maximal_vector V n E hE ⊤
    (fun _ _ _ _ => Submodule.mem_top) top_ne_bot
  have hc := Formalism.FourierDecayAlt.P.HighestWeightPolynomials.hw_cpol (m := m) hE (Qr.mem_CapSp.2 fun w => hq w v) hv0 hw
  have hroot : ∀ i, ∃ a : Fin n, m i = ν a - ((a : ℕ) : ℂ) := by
    intro i
    have h1 := hc (-m i)
    unfold Qr.cpol at h1
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by ring)] at h1
    obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.1 h1.symm
    exact ⟨a, by linear_combination -ha⟩
  have hdom : ∀ a b : Fin n, ∃ N : ℤ, ν a - ν b = (N : ℂ) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · obtain ⟨N, hN⟩ := Formalism.FourierDecayAlt.P.singular_dominant V n E ν v hE hw hv0 a b h
      exact ⟨N, by simpa using hN⟩
    · exact ⟨0, by simp [h]⟩
    · obtain ⟨N, hN⟩ := Formalism.FourierDecayAlt.P.singular_dominant V n E ν v hE hw hv0 b a h
      refine ⟨-N, ?_⟩
      push_cast
      linear_combination -hN
  intro i j
  obtain ⟨a, ha⟩ := hroot i
  obtain ⟨b, hb⟩ := hroot j
  obtain ⟨N, hN⟩ := hdom a b
  refine ⟨N - (a : ℕ) + (b : ℕ), ?_⟩
  push_cast
  linear_combination ha - hb + hN

end GlobalTheory.CompanionTheory.GapLie
end
