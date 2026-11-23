module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.SiegelGrowthForms.SiegelMult
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.Descend
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle565
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle097
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle656
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle527
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle098
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle115
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle595
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle128
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle075
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle077
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle526
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneAddInvPowMulRpowLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle078
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle574
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle250
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle184
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle079
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.SiegelGrowthForms.IsGrowFormEvAt
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.MirGen
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.ContinuousOnThetaCFunLtr
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.SgOneHd
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.TestFun
import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle006
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PositivityTheory.RgEis.Hd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem idTube : IdTube := GlobalTheory.T.identity_tube_holds
theorem tubeChain : TubeChain := GlobalTheory.T.tube_chain_holds
theorem secLaw : SecLaw := GlobalTheory.T.section_law_holds
theorem htLip : HtLip := GlobalTheory.T.height_lipschitz_holds
theorem stage : PiLocalization₂ := GlobalTheory.T.staged_estimate_holds
theorem wallLaw_of : SecLaw → WallLaw := GlobalTheory.T.wall_law_of_section_law
theorem cross_of : SecLaw → HtLip → PiLocalization₂ → WallLaw → Cross := GlobalTheory.T.crossing_of_walls_and_heights
theorem gallery_of : SecLaw → IdTube → TubeChain → Cross → Gallery := GlobalTheory.T.gallery_of_tubes_and_crossing
theorem transfer_of : SecLaw → WallLaw → Transfer := GlobalTheory.T.transfer_of_section_and_wall_laws
theorem twist_of : SecLaw → Twist := GlobalTheory.T.twist_of_section_law
theorem scale : Scale := GlobalTheory.T.eisenstein_scaling_law
theorem grpTop : GrpTop := GlobalTheory.T.general_linear_topological_group
theorem bdetLaw : BdetLaw := GlobalTheory.T.block_determinant_law
theorem extLaw : ExtLaw := GlobalTheory.T.extension_law
theorem parLaw_of : BdetLaw → ExtLaw → GrpTop → ParLaw := GlobalTheory.T.parabolic_law_of_block_det
theorem leviS_of : BdetLaw → ExtLaw → GrpTop → LeviS := GlobalTheory.T.levi_decomp_of_block_det
theorem leviQ_of : BdetLaw → ExtLaw → GrpTop → LeviQ := GlobalTheory.T.levi_quotient_of_block_det
theorem convGrOf_of : BdetLaw → ExtLaw → ConvGrOf := GlobalTheory.T.convergence_group_of_block_det
theorem convU_of : ParLaw → ConvU := GlobalTheory.T.unipotent_convergence_of_parabolic
theorem sgStep_of : Gallery → Transfer → Twist → GrpTop → ParLaw → LeviS → LeviQ → ConvGrOf → ConvU → SgStep := GlobalTheory.T.siegel_induction_from_gallery
theorem epConv : EpConv := GlobalTheory.CompanionTheory.EpConvB.epConv
theorem epMain_of : EpConv → EpMain := GlobalTheory.CompanionTheory.EpsteinMain.Hd.epMain_of_epConv
theorem testFun : TestFun := PositivityTheory.RgEis.TF.testFun
theorem testSph : TestSph := GlobalTheory.T.spherical_test_function_exists
theorem stdGood : StdGood := GlobalTheory.T.standard_section_good
theorem mirGen_of : SecLaw → StdGood → BdetLaw → EpConv → EpMain → TestFun → TestSph → MirGen := PositivityTheory.RgEis.MG.mirGen
theorem dict : Dict := GlobalTheory.T.local_global_dictionary
theorem dictInf : DictInf := GlobalTheory.T.archimedean_local_global_dictionary
theorem cmGood_of : StdGood → Dict → DictInf → CMGood := GlobalTheory.T.constant_multiplier_good
theorem cmMir_of : Dict → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw → MirGen → CMMir := GlobalTheory.T.constant_multiplier_mirabolic
theorem sgOne_of : SecLaw → WallLaw → Scale → StdGood → Dict → DictInf → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw →
    MirGen → SgOne := PositivityTheory.RgEis.So.sgOne_hd
theorem siegelMult_of : SecLaw → WallLaw → Dict → DictInf → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw → SgAll →
    SiegelEisensteinSeries.BRoad.SiegelMult := GlobalTheory.T.siegel_eisenstein_multiplicativity

theorem sgAll_of (hG : CMGood) (hM : CMMir) (h1 : SgOne) (hS : SgStep) : SgAll := by
  intro F E _ _ _ _ _ σ χ c h h' hχ hc ε
  suffices H : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n → 1 ≤ n → (adCM σ χ).Sg ε ι from
    fun ι _ _ hι => H _ ι rfl hι
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ι _ _ hι hn
    rcases Nat.eq_or_lt_of_le hn with e | e
    · exact h1 F E σ χ c h h' hχ hc ε ι (hι.trans e.symm)
    · exact hS E _ (adCM σ χ) (hG F E σ χ c h h' hχ hc) (hM F E σ χ c h h' hχ hc) ε ι (by omega)
        fun κ _ _ h1 h2 => ih _ (hι ▸ h2) κ rfl h1

theorem sgAll : SgAll :=
  have hW := wallLaw_of secLaw
  have hP := parLaw_of bdetLaw extLaw grpTop
  have hG := cmGood_of stdGood dict dictInf
  have hM := mirGen_of secLaw stdGood bdetLaw epConv (epMain_of epConv) testFun testSph
  sgAll_of hG (cmMir_of dict hG grpTop bdetLaw extLaw hP hM)
    (sgOne_of secLaw hW scale stdGood dict dictInf hG grpTop bdetLaw extLaw hP hM)
    (sgStep_of (gallery_of secLaw idTube tubeChain (cross_of secLaw htLip stage hW)) (transfer_of secLaw hW)
      (twist_of secLaw) grpTop hP (leviS_of bdetLaw extLaw grpTop) (leviQ_of bdetLaw extLaw grpTop)
      (convGrOf_of bdetLaw extLaw) (convU_of hP))

theorem eisBL : GlobalTheory.ThK.Dbl.EisBL :=
  have hW := wallLaw_of secLaw
  have hP := parLaw_of bdetLaw extLaw grpTop
  have hG := cmGood_of stdGood dict dictInf
  have hM := mirGen_of secLaw stdGood bdetLaw epConv (epMain_of epConv) testFun testSph
  SiegelEisensteinSeries.BRoad.eisBL_of GlobalTheory.T.eisenstein_half_holds
    (siegelMult_of secLaw hW dict dictInf hG grpTop bdetLaw extLaw hP
      (sgAll_of hG (cmMir_of dict hG grpTop bdetLaw extLaw hP hM)
        (sgOne_of secLaw hW scale stdGood dict dictInf hG grpTop bdetLaw extLaw hP hM)
        (sgStep_of (gallery_of secLaw idTube tubeChain (cross_of secLaw htLip stage hW)) (transfer_of secLaw hW)
          (twist_of secLaw) grpTop hP (leviS_of bdetLaw extLaw grpTop) (leviQ_of bdetLaw extLaw grpTop)
          (convGrOf_of bdetLaw extLaw) (convU_of hP))))
    GlobalTheory.CompanionTheory.Entire.local_factorisation

end PositivityTheory.RgEis.Hd
