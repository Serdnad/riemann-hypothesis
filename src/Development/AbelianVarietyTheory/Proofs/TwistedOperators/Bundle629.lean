module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftConstantTermCompatibleWeil
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle618
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle619
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle423
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle447
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle090
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle050
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle003
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle620
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaLift_constantTerm_compatibleWeil : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.TowerConstTermOfCompatible D := by
  first | exact @GlobalTheory.TowerCT.towerConstTermOfCompatible_holds | exact GlobalTheory.TowerCT.towerConstTermOfCompatible_holds | (intros; apply GlobalTheory.TowerCT.towerConstTermOfCompatible_holds <;> assumption)
end

section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.thetaVacuumCharacters_atRealPlaces : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D := by
  first | exact @GlobalTheory.vacChar_of_record | exact GlobalTheory.vacChar_of_record | (intros; apply GlobalTheory.vacChar_of_record <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaLift_lowerTower_vanishing : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.LowVanish D := by
  first | exact @GlobalTheory.LowVanishObj.lowVanish_obj | exact GlobalTheory.LowVanishObj.lowVanish_obj | (intros; apply GlobalTheory.LowVanishObj.lowVanish_obj <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.NTheta (IsIdemAt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section


theorem _root_.GlobalTheory.T.exists_rational_approx_finitePoint_vacuumLevel : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F),
    R.toLevCh.Is A.μ0 → R.IsFam → R.IsThP → ∀ (i : Fin D.R.m) (g : GA D (Wc D i)) (x : WO (Vc D i) (Wc D i)),
    x.map (infPart D) = 0 → ∃ (ℓ : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (w : WO (Vc D i) (Wc D i)),
      w.map (infPart D) = 0 ∧ heisO R.ψ (Vc D i) (Wc D i) w (R.vacP i) = R.vacP i ∧
      x = actO (Vc D i) (Wc D i) 1 g⁻¹ (ratW (Wc D i) (Vc D i) ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ) + w := by
  first | exact @GlobalTheory.FinApprox.exists_rat_approx | exact GlobalTheory.FinApprox.exists_rat_approx | (intros; apply GlobalTheory.FinApprox.exists_rat_approx <;> assumption)
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.NTheta (IsIdemAt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section


theorem _root_.GlobalTheory.T.heisenbergTranslate_vacuum_read_rationalPoints : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F),
    R.toLevCh.Is A.μ0 → R.IsFam → R.IsThP → ∀ (i : Fin D.R.m) (g : GA D (Wc D i)) (x : WO (Vc D i) (Wc D i)),
    x.map (infPart D) = 0 → ∀ (ℓ : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (w : WO (Vc D i) (Wc D i)),
    w.map (infPart D) = 0 → heisO R.ψ (Vc D i) (Wc D i) w (R.vacP i) = R.vacP i →
    x = actO (Vc D i) (Wc D i) 1 g⁻¹ (ratW (Wc D i) (Vc D i) ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ) + w →
    ∀ X : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E,
      R.ωP i A.μ0 (1, g) (heisO R.ψ (Vc D i) (Wc D i) x (R.vacP i)) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) X) =
        R.ψ (-(symplOH (Vc D i) (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) (X - ℓ)) +
            symplOH (Vc D i) (Wc D i) (ratW (Wc D i) (Vc D i) ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ) (actO (Vc D i) (Wc D i) 1 g w))) *
          R.ωP i A.μ0 (1, g) (R.vacP i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) (X - ℓ)) := by
  first | exact @GlobalTheory.HeisRatRead.heis_translate_read | exact GlobalTheory.HeisRatRead.heis_translate_read | (intros; apply GlobalTheory.HeisRatRead.heis_translate_read <;> assumption)
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

theorem _root_.GlobalTheory.T.isNonzeroFockVacuum_conj_unitVacuum_negSpace : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (f : WO S.V T.V → ℂ), GlobalTheory.Grid.IsVac ψ θ true S T f → GlobalTheory.Chain.IsVacVec ψ θ S.M T.M (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) := by
  first | exact @GlobalTheory.VacCjNeg.isVacVec_cj_of_isVac_neg | exact GlobalTheory.VacCjNeg.isVacVec_cj_of_isVac_neg | (intros; apply GlobalTheory.VacCjNeg.isVacVec_cj_of_isVac_neg <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

theorem _root_.GlobalTheory.T.conj_fockPureTensorMap_negFormSpace_eq : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (f : WO S.V T.V → ℂ), IsStdChar D ψ (-1) → IsInfFam θ → IsThetaFunO ψ (GlobalTheory.Grid.neg S.V) T.V f → ∀ P : GlobalTheory.Grid.Pol S T, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.Grid.fock ψ θ true S T f P) = GlobalTheory.Chain.ptOf ψ θ S.M T.M (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) (MvPolynomial.map (starRingEnd ℂ) P) := by
  first | exact @GlobalTheory.FockConjNeg.fock_neg_cj | exact GlobalTheory.FockConjNeg.fock_neg_cj | (intros; apply GlobalTheory.FockConjNeg.fock_neg_cj <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.splitPlace_latticeStabilisers_fix_weilVacuum : ∀ D : D7, SplitVacuumFixed D := by
  first | exact @GlobalTheory.PlaceTensor.splitVacuumFixed | exact GlobalTheory.PlaceTensor.splitVacuumFixed | (intros; apply GlobalTheory.PlaceTensor.splitVacuumFixed <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.ChiGrid
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Pointwise

namespace GlobalTheory.ModulUnit

variable {D : D7}

theorem exists_sep {v v' : GlobalTheory.FinPl.Pl D} (h : v' ≠ v) :
    ∃ t : 𝓞 D.host.F, t ∈ v'.asIdeal ∧ t ∉ v.asIdeal := by
  by_contra hc
  push_neg at hc
  exact h (HeightOneSpectrum.ext (v'.isMaximal.eq_of_le v.isPrime.ne_top hc))

theorem idV_eq_one_of_mem {v : GlobalTheory.FinPl.Pl D} {I : Ideal (𝓞 D.host.E)} {t : 𝓞 D.host.F} (ht : t ∉ v.asIdeal)
    (hI : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈ I) :
    GlobalTheory.SeeSaw.idV ((I : GlobalTheory.SeeSaw.FI D)) v = GlobalTheory.SeeSaw.idV 1 v := by
  refine le_antisymm (GlobalTheory.SeeSaw.idV_mono FractionalIdeal.coeIdeal_le_one v) ?_
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, h0, a, ha, rfl⟩
  obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
  obtain ⟨h1, h2⟩ := GlobalTheory.IdVGen.smul_inv_mem ht hα h0
  rw [GlobalTheory.IdVGen.tmul_eq ht α]
  refine AddSubgroup.subset_closure ⟨_, h1, h2, _, ?_, rfl⟩
  refine (FractionalIdeal.mem_coeIdeal _).2 ⟨_, I.mul_mem_right o hI, ?_⟩
  rw [map_mul]
  rfl

theorem idV_mul_of_eq_one {𝔞 I : GlobalTheory.SeeSaw.FI D} {v : GlobalTheory.FinPl.Pl D}
    (h : GlobalTheory.SeeSaw.idV I v = GlobalTheory.SeeSaw.idV 1 v) : GlobalTheory.SeeSaw.idV (𝔞 * I) v = GlobalTheory.SeeSaw.idV 𝔞 v := by
  rcases eq_or_ne 𝔞 0 with rfl | h0
  · rw [zero_mul]
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔞 h0
  have := GlobalTheory.SeeSaw.IdVMul.idV_mul_gen D v 𝔞 I x 1 hx0 one_ne_zero hx
    (GlobalTheory.Core.Mi.LatMatch.DiUnit.eq_one_iff.1 h)
  rw [mul_one] at this
  ext s
  rw [this, hx]

variable {T : Type} {L : LevCh D T}

theorem exists_mem_modul (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D} (hv : v ∉ P.S0) :
    ∃ s : 𝓞 D.host.F, s ∉ v.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ P.modul sc := by
  classical
  have hsep : ∀ v' ∈ P.S0, ∃ t : 𝓞 D.host.F, t ∈ v'.asIdeal ∧ t ∉ v.asIdeal :=
    fun v' hv' => exists_sep fun e => hv (e ▸ hv')
  choose! t ht using hsep
  refine ⟨∏ v' ∈ P.S0, t v' ^ P.depth sc v', fun hm => ?_, ?_⟩
  · obtain ⟨v', hv', hm'⟩ := (haveI := v.isPrime; Ideal.IsPrime.prod_mem_iff.1 hm)
    exact (ht v' hv').2 (v.isPrime.mem_of_pow_mem _ hm')
  · rw [map_prod]
    refine Ideal.prod_mem_prod fun v' hv' => ?_
    rw [map_pow]
    refine Ideal.pow_mem_pow ?_ _
    have h : t v' ∈ ((P.w v').under (𝓞 D.host.F)).asIdeal := by rw [P.under_w hv']; exact (ht v' hv').1
    exact h
end GlobalTheory.ModulUnit

namespace GlobalTheory.ModulUnit

variable {D : D7} {T : Type} {L : LevCh D T}

theorem conj_smul_algebraMap (s : 𝓞 D.host.F) :
    D.host.conj • algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s := by
  apply RingOfIntegers.ext
  show D.host.conj ((s : D.host.F) : D.host.E) = ((s : D.host.F) : D.host.E)
  exact (D.host.conjE_mem_hostF_iff _).1 (s : D.host.F).2

theorem exists_mem_modulBar (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D} (hv : v ∉ P.S0) :
    ∃ s : 𝓞 D.host.F, s ∉ v.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ P.modulBar sc := by
  obtain ⟨s, hs, hm⟩ := exists_mem_modul P sc hv
  refine ⟨s, hs, ?_⟩
  have := Ideal.smul_mem_pointwise_smul D.host.conj _ _ hm
  rwa [conj_smul_algebraMap] at this

end GlobalTheory.ModulUnit


open GlobalTheory.ModulUnit in
theorem GlobalTheory.ChiGrid.Places.idV_mul_modul : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : GlobalTheory.ChiGrid.Places L) (sc : GlobalTheory.ChiGrid.Consts) (v : GlobalTheory.FinPl.Pl D), v ∉ P.S0 → ∀ 𝔞 : GlobalTheory.SeeSaw.FI D, GlobalTheory.SeeSaw.idV (𝔞 * ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)) v = GlobalTheory.SeeSaw.idV 𝔞 v ∧ GlobalTheory.SeeSaw.idV (𝔞 * ((P.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)) v = GlobalTheory.SeeSaw.idV 𝔞 v := by
  intro D T L P sc v hv 𝔞
  obtain ⟨s, hs, hm⟩ := exists_mem_modul P sc hv
  obtain ⟨s', hs', hm'⟩ := exists_mem_modulBar P sc hv
  exact ⟨idV_mul_of_eq_one (idV_eq_one_of_mem hs hm), idV_mul_of_eq_one (idV_eq_one_of_mem hs' hm')⟩
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.StairIdealAt

theorem completion_eq_of_modul_unit : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (ρ : ℕ) (v : GlobalTheory.FinPl.Pl D), 0 < ρ → GlobalTheory.SeeSaw.idV ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) v = GlobalTheory.SeeSaw.idV 1 v → (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (ρ - 1 + 1))⁻¹ * (P.stA sc ^ (2 * ρ - (ρ - 1)) * (P.stAbar sc ^ (ρ - 1 + 1))⁻¹) ≠ 0) ∧ (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (ρ + 1))⁻¹ * (P.stA sc ^ (ρ + 1) * (P.stAbar sc ^ (ρ + 1))⁻¹) ≠ 0) ∧ ∀ s, s ∈ GlobalTheory.SeeSaw.idV ((D.host.AAbar : GlobalTheory.SeeSaw.FI D) * (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (ρ - 1 + 1))⁻¹ * (P.stA sc ^ (2 * ρ - (ρ - 1)) * (P.stAbar sc ^ (ρ - 1 + 1))⁻¹))⁻¹) v ↔ s ∈ GlobalTheory.SeeSaw.idV (FractionalIdeal.spanSingleton _ D.host.xi0⁻¹ * (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (ρ + 1))⁻¹ * (P.stA sc ^ (ρ + 1) * (P.stAbar sc ^ (ρ + 1))⁻¹))⁻¹) v := by
  intro D T L P sc ρ v hρ hM
  have hx : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hAb : (D.host.AAbar : GlobalTheory.SeeSaw.FI D) ≠ 0 := GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D
  have hMo : ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact P.modul_ne_bot sc
  have hS : P.stA sc ≠ 0 := ((GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L P sc).1
  have hT : P.stAbar sc ≠ 0 := mul_ne_zero hAb (inv_ne_zero hMo)
  have e1 : ρ - 1 + 1 = ρ := by omega
  have e2 : 2 * ρ - (ρ - 1) = ρ + 1 := by omega
  have hneg : ∀ k : ℕ, FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ ((-D.host.xi0) ^ k)⁻¹ =
      (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 ^ k)⁻¹ := by
    intro k
    rw [← FractionalIdeal.spanSingleton_inv, ← FractionalIdeal.spanSingleton_pow]
    congr 1
    congr 1
    apply FractionalIdeal.spanSingleton_eq_spanSingleton.2
    refine ⟨-1, ?_⟩
    rw [Units.smul_def]
    simp
  rw [e1, e2, hneg, hneg]
  set X := FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 with hXdef
  have hX : X ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.2 hx
  refine ⟨mul_ne_zero (inv_ne_zero (pow_ne_zero _ hX)) (mul_ne_zero (pow_ne_zero _ hS) (inv_ne_zero (pow_ne_zero _ hT))),
    mul_ne_zero (inv_ne_zero (pow_ne_zero _ hX)) (mul_ne_zero (pow_ne_zero _ hS) (inv_ne_zero (pow_ne_zero _ hT))), ?_⟩
  have key : (D.host.AAbar : GlobalTheory.SeeSaw.FI D) * ((X ^ ρ)⁻¹ * (P.stA sc ^ (ρ + 1) * (P.stAbar sc ^ ρ)⁻¹))⁻¹ *
      ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ =
      FractionalIdeal.spanSingleton _ D.host.xi0⁻¹ * ((X ^ (ρ + 1))⁻¹ * (P.stA sc ^ (ρ + 1) * (P.stAbar sc ^ (ρ + 1))⁻¹))⁻¹ := by
    rw [← FractionalIdeal.spanSingleton_inv, ← hXdef]
    have hTd : P.stAbar sc = D.host.AAbar * ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ := rfl
    rw [hTd]
    simp only [mul_inv, inv_inv, pow_succ, mul_pow]
    calc _ = (X⁻¹ * X) * (D.host.AAbar * ((X ^ ρ) * ((P.stA sc ^ ρ * P.stA sc)⁻¹ * ((D.host.AAbar : GlobalTheory.SeeSaw.FI D) ^ ρ *
          (((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) ^ ρ))) * ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) := by
          rw [inv_mul_cancel₀ hX, one_mul, mul_inv]
      _ = _ := by ring
  have hB0 : (D.host.AAbar : GlobalTheory.SeeSaw.FI D) * ((X ^ ρ)⁻¹ * (P.stA sc ^ (ρ + 1) * (P.stAbar sc ^ ρ)⁻¹))⁻¹ ≠ 0 :=
    mul_ne_zero hAb (inv_ne_zero (mul_ne_zero (inv_ne_zero (pow_ne_zero _ hX))
      (mul_ne_zero (pow_ne_zero _ hS) (inv_ne_zero (pow_ne_zero _ hT)))))
  obtain ⟨y, hy0, hy⟩ := GlobalTheory.IdVGen.idV_gen D v _ hB0
  have h1 := GlobalTheory.Core.Mi.LatMatch.DiUnit.eq_one_iff.1 (GlobalTheory.Core.Mi.LatMatch.DiUnit.inv_eq_one hM)
  have hp := GlobalTheory.SeeSaw.IdVMul.idV_mul_gen D v _ _ y 1 hy0 one_ne_zero hy h1
  rw [mul_one, key] at hp
  intro s
  rw [hp, hy]

end GlobalTheory.StairIdealAt
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin


theorem _root_.GlobalTheory.T.modulus_ideal_off_S0_trivial : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (v : GlobalTheory.FinPl.Pl D), v ∉ P.S0 → GlobalTheory.SeeSaw.idV ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) v = GlobalTheory.SeeSaw.idV 1 v := by
  first | exact @GlobalTheory.ModulUnit.idV_modul_eq_one | exact GlobalTheory.ModulUnit.idV_modul_eq_one | (intros; apply GlobalTheory.ModulUnit.idV_modul_eq_one <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.liftScalarIdentity_offFixedPlace_baseLevel : GlobalTheory.Hk3.HoweUnram → GlobalTheory.LowRow.ConjRatLift5 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ), A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → GlobalTheory.ConjScalar.ConjScalarAt R.toRealDat → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => (cj (twAt D.what₂.embLL A3.A.v0) (R.phs i))) i) → R.toRealDat.LUnif → ((R.toCx3 F).H5 F.cr false ∧ (R.toCx3 F).RATth F.cr false ∧ (R.toCx3 F).H3W F.cr false ∧ (lv (F.fc (R.toCx3 F).zs) false).Proviso) → (R.toCx3 F).GalD F.cr false := by
  first | exact @GlobalTheory.ConjScalarOff.galD_base | exact GlobalTheory.ConjScalarOff.galD_base | (intros; apply GlobalTheory.ConjScalarOff.galD_base <;> assumption)
end
