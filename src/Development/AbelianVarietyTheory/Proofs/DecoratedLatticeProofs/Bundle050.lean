module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHondaTypeEvenFrobeniusPowers
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsScalarMulIntegralOfNormalizesSymmetricLevel
public import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
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

@[expose] public section

section

open PowerSeries GlobalTheory.Honda

theorem _root_.GlobalTheory.T.isIntegralHondaLogarithmPair_shortWeierstrass : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 : K), ‖(2 : K)‖ = 1 → ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 → IntLog (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW g2 g3)) (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW g2 g3)) := by
  first | exact @GlobalTheory.Honda.intLog_shortW | exact GlobalTheory.Honda.intLog_shortW | (intros; apply GlobalTheory.Honda.intLog_shortW <;> assumption)
end

section

open PowerSeries GlobalTheory.Honda

theorem _root_.GlobalTheory.T.exists_hondaType_evenFrobeniusPowers : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K), Unr K l σ → ∀ (f e : K⟦X⟧), IntLog f e → ∀ w : K, CoefLe 1 (Formalism.L2.Th1.C.mulBy f e w) → σ (σ w) = w → ‖σ w - w‖ = 1 → ∃ c : ℕ → K, (∀ j, ‖c j‖ ≤ 1) ∧ CoefLe ‖(l : K)‖ (C (l : K) * f - hondaSum (σ ^ 2) (l ^ 2) c f) := by
  first | exact @GlobalTheory.Honda.exists_even_type | exact GlobalTheory.Honda.exists_even_type | (intros; apply GlobalTheory.Honda.exists_even_type <;> assumption)
end

section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

theorem _root_.GlobalTheory.T.maxUnramified_residueAlgClosed_and_frobeniusLift : ∀ (l : ℕ) [Fact l.Prime], 2 < l → ResAlg (MaximalUnramifiedExtension l) ∧ ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, Formalism.InvariantFactorPaths.G7.UnrOK (MaximalUnramifiedExtension l) l σ → Unr (MaximalUnramifiedExtension l) l σ := by
  first | exact @GlobalTheory.Honda.kur_resAlg_unr | exact GlobalTheory.Honda.kur_resAlg_unr | (intros; apply GlobalTheory.Honda.kur_resAlg_unr <;> assumption)
end

section

open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

theorem _root_.GlobalTheory.T.isScalarMul_integral_of_normalizes_symmetricLevel : ∀ (K : Type) [Field K] (O : ValuationSubring K) (k : Type) [Field k] (r : O →+* k), Function.Surjective r → ∀ (n ρ κ : ℕ), n = 2 * ρ + κ + 1 → 1 ≤ ρ → ∀ ψ : AddChar k ℂ, ψ ≠ 1 → ∀ a : Fin n → Fin n → k, (∀ i j, symEdge ρ κ i j → a i j ≠ 0) → ∀ m : GL (Fin n) K, (∀ x : GL (Fin n) O, bc r x ∈ unipSym k n ρ κ → ∃ x' : GL (Fin n) O, bc O.subtype x' = m * bc O.subtype x * m⁻¹ ∧ ψ (edgeVal ρ κ a (bc r x')) = ψ (edgeVal ρ κ a (bc r x))) → (∀ x : GL (Fin n) O, bc r x ∈ unipSym k n ρ κ → ∃ x' : GL (Fin n) O, bc O.subtype x' = m⁻¹ * bc O.subtype x * m) → IsScal O m := by
  first | exact @GlobalTheory.ScalInt.isScal_of_normalises | exact GlobalTheory.ScalInt.isScal_of_normalises | (intros; apply GlobalTheory.ScalInt.isScal_of_normalises <;> assumption)
end

section

open Module NumberField Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Rows Formalism.L2.Indef
open scoped Matrix ComplexOrder

namespace GlobalTheory.Core.AmbTieStep

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem hAt_eq_dot {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (x y : Fin n → K) :
    hAt H v x y = star (fun i => v.embedding (x i)) ⬝ᵥ (H.map v.embedding) *ᵥ (fun i => v.embedding (y i)) := by
  simp only [hAt, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Pi.star_apply, mul_assoc]

end GlobalTheory.Core.AmbTieStep
end
