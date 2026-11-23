module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryScalarMulIntegralLocalToGlobal
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasSumSphericalFunctionDoublingLength
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle044
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
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle022
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle003

@[expose] public section

section

open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

theorem _root_.GlobalTheory.T.unitary_scalarMulIntegral_local_to_global : ∀ {A : Type} [CommRing A] {S : Subring A} {P : Type} {k : P → Type} [∀ Q, Field (k Q)] {r : ∀ Q, S →+* k Q} (Z : PlaceSys A S P k r) (σ : A →+* A), (∀ a, σ (σ a) = a) → (∀ a ∈ S, σ a ∈ S) → ∀ (n : ℕ) (G : GL (Fin n) S) (m : GL (Fin n) A), m ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) → (∀ Q, IsScal (Z.O Q) (bc (Z.p Q) m) ∨ ∃ Q', σ (Z.e Q') = Z.e Q ∧ IsScal (Z.O Q') (bc (Z.p Q') m)) → ∃ (z : A) (x : GL (Fin n) S), z * σ z = 1 ∧ (m : Matrix (Fin n) (Fin n) A) = z • ((bc S.subtype x : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) := by
  first | exact @GlobalTheory.LevNorm.PlaceSys.unitary_locScal_glue | exact GlobalTheory.LevNorm.PlaceSys.unitary_locScal_glue | (intros; apply GlobalTheory.LevNorm.PlaceSys.unitary_locScal_glue <;> assumption)
end

section

open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling


theorem _root_.GlobalTheory.T.hasSum_sphericalFunction_doublingLength : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ) (φ : GL (Fin n) k → ℂ), IsBorelSph k γ φ → (∀ i, γ i ≠ 0) → ∀ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k → ∀ len : GL (Fin n) k → ℕ, (∀ e : Fin n → ℤ, Antitone e → ∀ g ∈ cell k (Fin n) ϖ e, len g = (∑ i, |e i|).toNat) → ∃ δ : ℝ, 0 < δ ∧ ∀ X : ℂ, ‖X‖ < δ → HasSum (fun c : GL (Fin n) k ⧸ KO k (Fin n) => X ^ len c.out * φ c.out) ((∏ i : Fin n, (1 - (resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X)⁻¹) * (∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X)⁻¹) * ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * X ^ 2)) := by
  first | exact @GlobalTheory.DoublingLength.hasSum_doublingLength | exact GlobalTheory.DoublingLength.hasSum_doublingLength | (intros; apply GlobalTheory.DoublingLength.hasSum_doublingLength <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.kStable_submodule_eq_top_of_highestWeight_le : ∀ (p q : ℕ) (M : GKMod p q) (N : Submodule ℂ M.V), KStable M.act N → (∀ μ, hwSub M.act μ ≤ N) → N = ⊤ := by
  first | exact @GlobalTheory.HwSpan.eq_top_of_hwSub_le | exact GlobalTheory.HwSpan.eq_top_of_hwSub_le | (intros; apply GlobalTheory.HwSpan.eq_top_of_hwSub_le <;> assumption)
end

section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

theorem _root_.GlobalTheory.T.exists_unramified_near_integral_complexPadic : ∀ (l : ℕ) [Fact l.Prime] (x : ℂ_[l]), ‖x‖ ≤ 1 → ∃ y ∈ MaximalUnramifiedExtension l, ‖y‖ ≤ 1 ∧ ‖x - y‖ < 1 := by
  first | exact @GlobalTheory.ResidueUnr.exists_near_kur | exact GlobalTheory.ResidueUnr.exists_near_kur | (intros; apply GlobalTheory.ResidueUnr.exists_near_kur <;> assumption)
end

section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

theorem _root_.GlobalTheory.T.exists_homothetic_periodPair_lattice : ∀ (L : PeriodPair) (c : ℂ), c ≠ 0 → ∃ L' : PeriodPair, (∀ z, z ∈ L'.lattice ↔ c * z ∈ L.lattice) ∧ L'.g₂ = c ^ 4 * L.g₂ ∧ L'.g₃ = c ^ 6 * L.g₃ ∧ (∀ z, L'.weierstrassP z = c ^ 2 * L.weierstrassP (c * z) ∧ L'.derivWeierstrassP z = c ^ 3 * L.derivWeierstrassP (c * z)) ∧ ∀ d, HasCMBy d L → HasCMBy d L' := by
  first | exact @GlobalTheory.homotheticLattice | exact GlobalTheory.homotheticLattice | (intros; apply GlobalTheory.homotheticLattice <;> assumption)
end
