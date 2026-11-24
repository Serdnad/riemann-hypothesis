module

import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateIntertwinerValuesIsCuspFun
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountedVectorIsCuspForm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalFrame
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalOfConvolutionFixedModerateGrowth
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousRepresentativeBoundedEvaluation
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalConvolutionOrthogonalProjectorProof
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealUnipotentIntegralDiscreteSeriesVanish
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompletedTensorDiscreteSeriesIrreducibleFormalDe
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalSubspaceClosedRightTranslationStable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCoefficientIntegrableMajorant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralInvOfSupport
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Algebra.Order.Star.Real

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountedVectorsAreCuspFormsSingleLowestKType, Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdempotentIntertwinerImagesCuspidalOfLevel

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountedVectorsAreCuspFormsSingleLowestKType =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountedVectorsAreCuspFormsSingleLowestKType", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne\npublic import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalOfConvolutionFixedModerateGrowth\npublic import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousRepresentativeBoundedEvaluation\npublic import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalConvolutionOrthogonalProjectorProof\npublic import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealUnipotentIntegralDiscreteSeriesVanish\nimport Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCoefficientIntegrableMajorant\nimport Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralInvOfSupport\nimport Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.RowCuspKType

private theorem one_mem_Kg_flag_measures (I : AutInst) (g : ℕ) : (1 : I.Gf) ∈ I.Kg g := by
  refine ⟨?_, fun y _ => ⟨0, Submodule.zero_mem _, ?_⟩⟩
  · show (1 : I.Gf) ∈ I.Kset
    simp only [AutInst.Kset, Set.mem_ofPred_eq, OneMemClass.coe_one]
    exact one_mem _
  · simp only [AutInst.fmat, OneMemClass.coe_one, Units.val_one, sub_self, Matrix.zero_mulVec, smul_zero]

theorem level_comp_Re (B : RowsAut) (k : B.I.Gf) (hk : k ∈ B.I.Kg B.g) (hg : 1 ≤ B.g) :
    (B.R (1, k)).comp B.Re = B.Re := by
  first | exact _root_.GlobalTheory.RowCusp.level_comp_Re | exact @_root_.GlobalTheory.RowCusp.level_comp_Re | apply _root_.GlobalTheory.RowCusp.level_comp_Re <;> assumption

theorem integrable_ph (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ) (hd : IsDSData B d) (hn : 1 ≤ B.I.n)
    (hh : ∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) (hl : LocDec B h) :
    Integrable (ph B d) (muInf B.I) := by
  first | exact _root_.GlobalTheory.RowCusp.integrable_ph | exact @_root_.GlobalTheory.RowCusp.integrable_ph | apply _root_.GlobalTheory.RowCusp.integrable_ph <;> assumption

theorem row_isCuspFn : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → 1 ≤ B.g → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h → HBig B 40 h → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ A ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (A (B.tens B.w))) := by
  intro B d h hd hK hg hh hl hbig T hT A hA
  rcases Nat.eq_zero_or_pos B.I.n with hn0 | hnpos
  · intro W hW
    have : IsEmpty (Fin B.I.n) := by rw [hn0]; infer_instance
    exact absurd (Submodule.eq_bot_of_subsingleton) hW.1
  have hn : 1 ≤ B.I.n := hnpos
  have hint := integrable_ph B d h hd hn hh hl
  obtain ⟨-, hcomm, -, hT'⟩ := GlobalTheory.GlobProj.globalProj_holds B d hd hint
  have hfix : T (A (B.tens B.w)) = A (B.tens B.w) := (hT' T hT).2.1 A hA
  obtain ⟨A₀, hA₀, hAe⟩ := Submodule.mem_map.mp hA
  have hAe' : A = B.Re.comp A₀ := by rw [← hAe]; rfl
  subst hAe'
  have hA₀' : ∀ g : B.I.Ginf, A₀.comp (B.σs g) = (B.R (g, 1)).comp A₀ := hA₀
  have hhom : B.Re.comp A₀ ∈ B.I.HomS B.σs B.μf B.fund B.R := by
    show ∀ g : B.I.Ginf, (B.Re.comp A₀).comp (B.σs g) = (B.R (g, 1)).comp (B.Re.comp A₀)
    intro g
    rw [ContinuousLinearMap.comp_assoc, hA₀' g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]
  have hlev : ∀ k ∈ B.I.Kg B.g, B.R (1, k) ((B.Re.comp A₀) (B.tens B.w)) = (B.Re.comp A₀) (B.tens B.w) := by
    intro k hk
    rw [ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply (B.R (1, k)) B.Re,
      level_comp_Re B k hk hg]
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.EvalBound.exists_contRep_bound_of_isKTypeOf B d hd hK hn hg
  obtain ⟨f, hf, hfb⟩ := hC _ hhom hlev
  have hvan := _root_.GlobalTheory.RealFibre.integral_phe_eq_zero_of_isKTypeOf B d h hd hK hl hh
  refine (_root_.GlobalTheory.CuspFixed.cusp_of_fixed B d h hd hvan hl hbig T hT _ f (C * ‖(B.Re.comp A₀) (B.tens B.w)‖) ?_ hf ?_).2
  · simpa using hfix
  · intro x
    exact (hfb x).trans_eq (by ring)

end GlobalTheory.RowCuspKType
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountedVectorsAreCuspFormsSingleLowestKType =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdempotentIntertwinerImagesCuspidalOfLevel =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdempotentIntertwinerImagesCuspidalOfLevel", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne\npublic import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompletedTensorDiscreteSeriesIrreducibleFormalDe\npublic import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountedVectorsAreCuspFormsSingleLowestKType\npublic import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalSubspaceClosedRightTranslationStable\nimport Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCoefficientIntegrableMajorant\nimport Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalConvolutionOrthogonalProjectorProof\nimport Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralInvOfSupport\nimport Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.Dec.CuspAllKType

theorem one_mem_Kg (I : AutInst) (g : ℕ) : (1 : I.Gf) ∈ I.Kg g := by
  apply _root_.GlobalTheory.RowCuspKType.one_mem_Kg_flag_measures <;> assumption

theorem re_fixed (B : RowsAut) : ∀ k ∈ B.I.Kg B.g, (B.R (1, k)).comp B.Re = B.Re := by
  first | exact _root_.GlobalTheory.Dec.CuspFrame.re_fixed | exact @_root_.GlobalTheory.Dec.CuspFrame.re_fixed | apply _root_.GlobalTheory.Dec.CuspFrame.re_fixed <;> assumption

theorem integrable_ph (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ) (hd : IsDSData B d)
    (hl : LocDec B h) (hb : HBig B 40 h) : Integrable (ph B d) (muInf B.I) := by
  first | exact _root_.GlobalTheory.Dec.CuspAll.integrable_ph | exact @_root_.GlobalTheory.Dec.CuspAll.integrable_ph | apply _root_.GlobalTheory.Dec.CuspAll.integrable_ph <;> assumption

theorem cusp_all : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → 1 ≤ B.g → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h → HBig B 40 h → ∀ A ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re, A ∈ B.I.HomS B.σs B.μf B.fund B.R ∧ ∀ u, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (A u)) ∧ ∀ k ∈ B.I.Kg B.g, B.R (1, k) (A u) = A u := by
  intro B d h hd hK hg hh hl hb A hA

  obtain ⟨T0, hT0, hA'⟩ := Submodule.mem_map.1 hA
  have hAe : A = B.Re.comp T0 := by rw [← hA']; rfl
  subst hAe
  have hT0' : ∀ g : B.I.Ginf, T0.comp (B.σs g) = (B.R (g, 1)).comp T0 := hT0
  have hint := integrable_ph B d h hd hl hb
  obtain ⟨-, hcomm, ⟨T, hT⟩, -⟩ := GlobalTheory.GlobProj.globalProj_holds B d hd hint
  have hHom : ∀ g : B.I.Ginf, (B.Re.comp T0).comp (B.σs g) = (B.R (g, 1)).comp (B.Re.comp T0) := fun g => by
    rw [ContinuousLinearMap.comp_assoc, hT0' g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]
  refine ⟨hHom, fun u => ?_⟩

  obtain ⟨S, hSmem, hScl, hSinv, -⟩ := GlobalTheory.CuspSubspace.cuspidal_closed_stable B
  obtain ⟨-, hirr, -, hnorm, -⟩ := GlobalTheory.Dec.tensorRep B d hd
  have hw := _root_.GlobalTheory.RowCuspKType.row_isCuspFn B d h hd hK hg hh hl hb T hT (B.Re.comp T0) hA
  let S' : Submodule ℂ B.Hs := S.comap ((B.Re.comp T0 : B.Hs →L[ℂ] B.I.L2 B.μf B.fund) : B.Hs →ₗ[ℂ] B.I.L2 B.μf B.fund)
  have hS'cl : IsClosed (S' : Set B.Hs) := hScl.preimage (B.Re.comp T0).continuous
  have hS'inv : ∀ g, ∀ v ∈ S', B.σs g v ∈ S' := fun g v hv => by
    have hv' : (B.Re.comp T0) v ∈ S := hv
    show (B.Re.comp T0) (B.σs g v) ∈ S
    have := congrArg (fun F : B.Hs →L[ℂ] B.I.L2 B.μf B.fund => F v) (hHom g)
    simp only [ContinuousLinearMap.comp_apply] at this
    simp only [ContinuousLinearMap.comp_apply]
    rw [this]
    exact hSinv _ _ hv'
  have hwS : B.tens B.w ∈ S' := (hSmem _).2 hw
  rcases hirr S' hS'cl hS'inv with h0 | htop
  · exfalso
    rw [h0, Submodule.mem_bot] at hwS
    rw [hwS, norm_zero] at hnorm
    exact zero_ne_one hnorm
  · have hu : u ∈ S' := htop ▸ Submodule.mem_top
    refine ⟨(hSmem _).1 hu, fun k hk => ?_⟩
    rw [ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply (B.R (1, k)) B.Re, re_fixed B k hk]

end GlobalTheory.Dec.CuspAllKType
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdempotentIntertwinerImagesCuspidalOfLevel =====
