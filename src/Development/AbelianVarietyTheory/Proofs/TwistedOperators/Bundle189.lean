module

public import Formalism.SatakeDualWeyl.Statement
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle174
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.eq_one_of_finiteOrder_unipotentReduction_largePrime : ∀ (E R k : Type) [Field E] [NumberField E] [CommRing R] [CommRing k] (S : Subring R) (ι : E →+* R) (φ : S →+* k) (p n : ℕ), p.Prime → CharP k p → Module.finrank ℚ E * n + 1 < p → ∀ (u : GL (Fin n) E) (x : GL (Fin n) R) (y : GL (Fin n) S), IsOfFinOrder u → Formalism.UG.bc S.subtype y = x⁻¹ * Formalism.UG.bc ι u * x → IsNilpotent ((Formalism.UG.bc φ y : GL (Fin n) k).val - 1) → u = 1 := by
  first | exact @GlobalTheory.UnipRed.eq_one_of_unipotent_reduction | exact GlobalTheory.UnipRed.eq_one_of_unipotent_reduction | (intros; apply GlobalTheory.UnipRed.eq_one_of_unipotent_reduction <;> assumption)
end

section

open GlobalTheory.Orb
open scoped Topology ContDiff Manifold

noncomputable section

namespace GlobalTheory

theorem glue_smooth_of_compactSupport : ∀ (H : Type) [TopologicalSpace H] (X : Type) [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] (c : H → X) (f : H → ℂ), Continuous c →
    HasCompactSupport f →
    (∀ a, ∃ V : Set X, IsOpen V ∧ c a ∈ V ∧ ∃ Φ : X → ℂ, ContDiffOn ℝ ∞ Φ V ∧
      ∀ g, c g ∈ V → f g = Φ (c g)) →
    ∃ Φ : X → ℂ, ContDiff ℝ ∞ Φ ∧ ∀ g, f g = Φ (c g) := by
  intro H _ X _ _ _ c f hc hf hloc
  choose V hVo hcV Φ hΦ hfΦ using hloc
  have hs : IsClosed (c '' tsupport f) := (hf.isCompact.image hc).isClosed
  have hcov : c '' tsupport f ⊆ ⋃ a, V a := by
    rintro _ ⟨a, -, rfl⟩
    exact Set.mem_iUnion.2 ⟨a, hcV a⟩
  obtain ⟨χ, hχ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, X) hs V hVo hcov
  refine ⟨fun y => ∑ᶠ a, χ a y • Φ a y, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    refine χ.contDiffAt_finsum fun a hy => ?_
    exact (hΦ a).contDiffAt ((hVo a).mem_nhds (hχ a hy))
  · intro g
    have hterm : ∀ a, χ a (c g) • Φ a (c g) = χ a (c g) • f g := by
      intro a
      by_cases h0 : χ a (c g) = 0
      · simp [h0]
      · have hmem : c g ∈ V a := hχ a (subset_tsupport _ h0)
        rw [hfΦ a g hmem]
    simp only [hterm]
    by_cases hg : g ∈ tsupport f
    · rw [← finsum_smul, χ.sum_eq_one ⟨g, hg, rfl⟩, one_smul]
    · have : f g = 0 := image_eq_zero_of_notMem_tsupport hg
      simp [this]

end GlobalTheory
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.free_monoidAlgebra_of_character_vanishes_off_one : ∀ (P M : Type) [Group P] [Finite P] [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ P M), (∀ g : P, g ≠ 1 → LinearMap.trace ℂ M (ρ g) = 0) → ∃ N : ℕ, Nat.card P * N = Module.finrank ℂ M ∧ Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra ℂ P] (Fin N → MonoidAlgebra ℂ P)) := by
  first | exact @GlobalTheory.FreeOfCharacter.free_of_trace_eq_zero | exact GlobalTheory.FreeOfCharacter.free_of_trace_eq_zero | (intros; apply GlobalTheory.FreeOfCharacter.free_of_trace_eq_zero <;> assumption)
end
