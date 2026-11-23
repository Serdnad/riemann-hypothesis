module

public import Formalism.FormalDegreeBessel.StatementRP
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelLiftBasics.LevelGroupUnitaryHermitian
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormCore
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HilbertSchmidtBlocks.HSBlocksMain
public import Formalism.PeriodIntegrals.Bundle014
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalHaarSubgroup.MemOrdR
public import Formalism.PeriodIntegrals.Bundle019
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle016
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle011
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle015
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmSkip
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BorderMinorRotation.QmBorderFullOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.Assemble
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.CapelliOps
public import Formalism.PeriodIntegrals.Bundle021
public import Formalism.PeriodIntegrals.Bundle004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.DetSplit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.LowerInv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.ModelMap
public import Formalism.PeriodIntegrals.Bundle025
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.VecVMulVec
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RealFieldComparison.JmMulApply
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

theorem level_basics : Formalism.QuantumDeterminants.LevHom ∧ Formalism.QuantumDeterminants.LevUH ∧ Formalism.QuantumDeterminants.LevN ∧ Formalism.QuantumDeterminants.LevUW ∧ Formalism.QuantumDeterminants.LevWb ∧ Formalism.QuantumDeterminants.LevEll :=
  ⟨PI.QnLevBasicsW.level_group_homomorphism, PI.QnLevBasicsW.level_group_unitary_hermitian, PI.QnLevBasicsW.level_group_nilpotent,
    PI.QnLevBasicsW.level_group_unitary_weyl, PI.QnLevBasicsW.level_group_isotropic_vector, PI.QnLevBasicsW.level_group_ellipticity⟩
end

section

private theorem eabH_comp_mul_left {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H h : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Formalism.QuantumDeterminants.EabH H a b (fun x => f (h * x)) = fun x => Formalism.QuantumDeterminants.EabH H a b f (h * x) := by
  funext g
  simp only [Formalism.QuantumDeterminants.EabH, Formalism.REAL.RdV, mul_assoc]

private theorem qdTop_eabH_comp_mul_left {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H h : Matrix (Fin n) (Fin n) ℂ) (u : ℂ) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Formalism.QuantumDeterminants.Top (Formalism.QuantumDeterminants.EabH H) u a b (fun x => f (h * x)) =
      fun x => Formalism.QuantumDeterminants.Top (Formalism.QuantumDeterminants.EabH H) u a b f (h * x) := by
  funext g
  simp only [Formalism.QuantumDeterminants.Top, eabH_comp_mul_left]

private theorem foldr_apply_comp_mul_left_of_forall_mem {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (h : Matrix (Fin n) (Fin n) ℂ) (L : List ((Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)))
    (hL : ∀ T ∈ L, ∀ f : Matrix (Fin n) (Fin n) ℂ → E, T (fun x => f (h * x)) = fun x => T f (h * x))
    (f : Matrix (Fin n) (Fin n) ℂ → E) :
    L.foldr (fun T g => T g) (fun x => f (h * x)) = fun x => L.foldr (fun T g => T g) f (h * x) := by
  induction L with
  | nil => rfl
  | cons T L ih =>
    simp only [List.foldr_cons]
    rw [ih (fun T' hT' => hL T' (by simp [hT']))]
    exact hL T (by simp) _

theorem qnMinorLeft : Formalism.FourierDecayAlt.Q.QMinorLeftH := by
  intro E _ _ n t H f a b u h
  funext x
  simp only [Formalism.QuantumDeterminants.qminorOp, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hL : ∀ T ∈ List.ofFn (fun k : Fin t =>
      Formalism.QuantumDeterminants.Top (Formalism.QuantumDeterminants.EabH H) (u - ((k : ℕ) : ℂ)) (a (σ k)) (b k)),
      ∀ f' : Matrix (Fin n) (Fin n) ℂ → E, T (fun x => f' (h * x)) = fun x => T f' (h * x) := by
    intro T hT f'
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hT
    exact qdTop_eabH_comp_mul_left H h _ _ _ f'
  rw [foldr_apply_comp_mul_left_of_forall_mem h _ hL f]

theorem quantum_minor_left : Formalism.FourierDecayAlt.Q.QMinorLeftH := qnMinorLeft
end

section

theorem hilbert_schmidt_blocks : Formalism.L2.SG.NormCut.HSBlocks :=
  NormHilbertSchmidtBlocks.hSBlocks_main
end

section

theorem local_haar_real_real : PI.LocHaarRR.Target := PI.LocHaarRRW.target
end

section

theorem quantum_minor_border_full : PI.QmBorderFull :=
  PI.qmBorderFull_of quantum_minor_border_es quantum_minor_column_expansion quantum_minor_row_expansion quantum_minor_skip
end

section

theorem hook_length_bound : PI.HookBound := PI.HookSteps.hookBound_of PI.HookSteps.Cap.capelli_determinant_identity
end

section

theorem modelIso_of : PI.PolyCoef → PI.UnitaryDense → PI.HwIrred → PI.ModelIso :=
  fun hp hu hh => PI.WMI.modelIso_of_steps (PI.WMI.polyExt_of hp hu) PI.WMI.lambda_integrality
    PI.WMI.torus_eigenvalue_formula PI.WMI.lower_triangular_invariance PI.WMI.model_map_equivariance PI.WMI.determinant_splitting_formula hh
end

section

theorem adelic_compact_finite_places : PI.AdBridgeSteps.FinK :=
  PI.FinKW.finK_of PI.FinKW.LocTo.mem_local_lattice_iff (PI.FinKW.memLocFrom_of PI.FinKW.local_vector_injective)
    PI.FinKW.local_vector_lift
end

section

theorem adelic_compact_real_places : PI.AdBridgeSteps.RealK := PI.UnitaryGroupMassFormula.BridgeRealK.realK
end
