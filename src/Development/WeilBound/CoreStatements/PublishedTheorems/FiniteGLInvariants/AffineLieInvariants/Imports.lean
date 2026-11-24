module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchLieDerivativeExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalGeneralizedSpaceSpanClosed
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGrowthUniform
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMonicAevalAddOfKill
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenLevel
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimOfAnnihilatingPolyEigenspaces
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteGeneralizedEigenspaceCofiniteDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAddHaarMeasureUnipMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLeftInvariantOfIsAutForm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOneLMemZalg
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearOdeValueDeterminedByShifts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemL2OfBoundedContinuousInvariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RapidDecayOfOneParabolicBounds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothAutomorphicOpenInvariant
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCentreDerivativeLieAction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCentreTranslatePreservesCuspSpace
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermFiniteOfSmaller
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericFiniteByInduction
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.TopEig
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMonicAevalMemOfLeSup
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantOfLieOneLEqZero

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.InvariantOfLieOneLEqZero, Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports

-- ===== clump member: Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.InvariantOfLieOneLEqZero =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.InvariantOfLieOneLEqZero", "h": "module\n\npublic import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL\npublic import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL\npublic import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchLieDerivativeExists\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalGeneralizedSpaceSpanClosed\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGrowthUniform\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMonicAevalAddOfKill\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenLevel\npublic import Mathlib.Algebra.Polynomial.AlgebraMap\npublic import Mathlib.Basic.Complex.Basic\npublic import Mathlib.LinearAlgebra.FiniteDimensional.Defs\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimOfAnnihilatingPolyEigenspaces\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteGeneralizedEigenspaceCofiniteDecomposition\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAddHaarMeasureUnipMeasure\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLeftInvariantOfIsAutForm\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOneLMemZalg\npublic import Mathlib.Algebra.Polynomial.Degree.Defs\npublic import Mathlib.Analysis.CStarAlgebra.Classes\npublic import Mathlib.Analysis.Calculus.Deriv.Basic\npublic import Mathlib.Analysis.InnerProductSpace.Basic\npublic import Mathlib.Analysis.LocallyConvex.AbsConvexOpen\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearOdeValueDeterminedByShifts\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemL2OfBoundedContinuousInvariant\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RapidDecayOfOneParabolicBounds\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothAutomorphicOpenInvariant\npublic import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCentreDerivativeLieAction\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCentreTranslatePreservesCuspSpace\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab\nimport Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMonicAevalMemOfLeSup\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Coalgebra.IsFrobenius\nimport Mathlib.RingTheory.HopfAlgebra.Basic\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace CuspFormAutomorphicBounds

theorem cuspRapidDecaySiegelGL : GlobalTheory.Published.CuspRapidDecaySiegelGL := by
  intro E _ _ _ a φ hφ
  have hs := GlobalTheory.CompanionTheory.ArchSmooth.sm_mem_archSmooth E a φ
  have hc : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E a φ hφ.1.level
  exact GlobalTheory.CompanionTheory.SiegelDecay.rapid_decay_of_one_parabolic_bounds E a φ.1 hc
    (_root_.GlobalTheory.CompanionTheory.GGPS.smooth_automorphic_open_invariant E a φ.1 hs (GlobalTheory.CompanionTheory.LeftInv.isLeftInvariant_of_isAutForm E a φ hφ.1)
      (GlobalTheory.CompanionTheory.AutLevel.exists_open_level E a φ hφ.1) (GlobalTheory.CompanionTheory.CuspBridge.isCuspidal_of_isCuspForm E a φ hφ)
      (GlobalTheory.CompanionTheory.HCRep.uJ_eq_conv E a φ hs hφ.1) (GlobalTheory.CompanionTheory.BoxBound.box_bound E a φ hφ.1))

theorem cuspFormsBoundedGL : GlobalTheory.Published.CuspFormsBoundedGL :=
  GlobalTheory.CuspBoundSiegel.cuspFormsBounded_of_rapidDecay cuspRapidDecaySiegelGL

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem cuspFin_zero : CuspFin E 0 := by
  intro L hL W _ _ _ ρ hρ J hJ
  haveI : Finite (GA E 0) := Finite.of_subsingleton
  haveI : FiniteDimensional ℂ (GA E 0 → ℂ) := inferInstance
  infer_instance

theorem invariant_of_lie_oneL_eq_zero {a : ℕ} (ψ : Sm E a) (h : lie E a (oneL E a) ψ = 0) (t : ℝ) (g : GA E a) :
    ψ.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = ψ.1 g := by
  rw [CuspidalL2GL.splitCentre_comm]
  have hd : ∀ s, HasDerivAt (fun s : ℝ => ψ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a s)) 0 s := by
    intro s
    have := _root_.GlobalTheory.CompanionTheory.CuspFinDeriv.hasDerivAt_splitCentre E a ψ g s
    rwa [h] at this
  have := is_const_of_deriv_eq_zero (f := fun s : ℝ => ψ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a s))
    (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  simpa [CuspidalL2GL.splitCentre_zero] using this

theorem cuspFin_pos {a : ℕ} (ha : 0 < a) : CuspFin E a := by
  apply _root_.GlobalTheory.CompanionTheory.CuspFinGL.Split.cuspFin_pos <;> assumption

theorem cuspFin : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), CuspFin E a := by
  intro E _ _ _ a
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact cuspFin_zero
  · exact cuspFin_pos ha

end CuspFormAutomorphicBounds
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.InvariantOfLieOneLEqZero =====

-- ===== clump member: Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports", "h": "module\n\npublic import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot\npublic import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermFiniteOfSmaller\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericFiniteByInduction\npublic import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.InvariantOfLieOneLEqZero\npublic import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.TopEig\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

theorem CuspFormAutomorphicBounds.automorphicFormsFiniteGL : GlobalTheory.Published.AutomorphicFormsFiniteGL :=
  PositivityTheory.Affgl.TopEig.top (_root_.GlobalTheory.CompanionTheory.AffglAssembly.genFin_of_chapters CuspFormAutomorphicBounds.cuspFin _root_.GlobalTheory.CompanionTheory.CTFin.ctFin)
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports =====
