module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightAtRealPlaceLeOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDimensionalThetaFunctionsLevelFockDegree
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle301
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle178
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle177
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle179
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle194
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.hasProd_partialLFunctionTwistedByChar_local_factors : ∀ (D : D7) (Sf : Finset (FinPl D)) (par : GlobalTheory.LFun.Fam D.host.E) (χ : (AE D)ˣ →* Circle) (r : ℕ) (κ : ℝ), GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (Sf : Set (FinPl D))) par r κ → ∀ z : ℂ, κ + 1 < z.re → HasProd (fun v : {v : FinPl D // v ∉ (Sf : Set (FinPl D))} => GlobalTheory.LFun.LvTw par (GlobalTheory.LFun.val χ) v.1 z) (GlobalTheory.LFun.LSD D Sf par χ z) := by
  first | exact @GlobalTheory.LSD_hasProd_LvTw | exact GlobalTheory.LSD_hasProd_LvTw | (intros; apply GlobalTheory.LSD_hasProd_LvTw <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open scoped TensorProduct


theorem _root_.GlobalTheory.T.ideleCharacter_eq_one_integral_units_unramified_adelic : ∀ (D : D7) (μ : (AE D)ˣ →* Circle) (v : FinPl D) (y : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ), (y : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈ intLoc D.host.F D.host.E v → ((y⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈ intLoc D.host.F D.host.E v → (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt μ w) → charAt μ v y = 1 := by
  first | exact @GlobalTheory.LFun.charAt_eq_one_of_unrAt_datum | exact GlobalTheory.LFun.charAt_eq_one_of_unrAt_datum | (intros; apply GlobalTheory.LFun.charAt_eq_one_of_unrAt_datum <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.SumBox

variable {D : D7}

def sumMat {B W H : HSp D} (o : OrthDec B W H) (sW : RealMat W) (sH : RealMat H) : RealMat B :=
  fun τ => o.iA.map (tauE D τ) * sW τ * o.qA.map (tauE D τ) + o.iB.map (tauE D τ) * sH τ * o.qB.map (tauE D τ)

def sumLatO {B W H : HSp D} (o : OrthDec B W H) (LW : Lat W) (LH : Lat H) : Lat B :=
  LW.map ((Matrix.mulVecLin o.iA).restrictScalars (𝓞 D.host.E)) ⊔
    LH.map ((Matrix.mulVecLin o.iB).restrictScalars (𝓞 D.host.E))

theorem sumMat_apply {B W H : HSp D} (o : OrthDec B W H) (sW : RealMat W) (sH : RealMat H) (τ : D.what₂.Tau) :
    sumMat o sW sH τ =
      o.iA.map (tauE D τ) * sW τ * o.qA.map (tauE D τ) + o.iB.map (tauE D τ) * sH τ * o.qB.map (tauE D τ) := rfl

theorem mem_sumLatO {B W H : HSp D} (o : OrthDec B W H) (LW : Lat W) (LH : Lat H) (y : Fin B.rank → D.host.E) :
    y ∈ sumLatO o LW LH ↔ ∃ x ∈ LW, ∃ x' ∈ LH, o.iA *ᵥ x + o.iB *ᵥ x' = y := by
  simp only [sumLatO, Submodule.mem_sup, Submodule.mem_map, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨x', hx', rfl⟩, rfl⟩
    exact ⟨x, hx, x', hx', rfl⟩
  · rintro ⟨x, hx, x', hx', rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, _, ⟨x', hx', rfl⟩, rfl⟩

end GlobalTheory.Core.Rk.SumBox
end
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.exists_adelicMajorantFrame_for_cartanInvolutions : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (sA : RealMat A), IsInfFam θ → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → ∃ a : GL (Fin A.rank) (AE D), IsMaj A a ∧ ∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D A τ * sA τ) * compAt θ τ a.1 = 1 := by
  first | exact @GlobalTheory.Core.Rk.MajFrame.exists_maj_cart | exact GlobalTheory.Core.Rk.MajFrame.exists_maj_cart | (intros; apply GlobalTheory.Core.Rk.MajFrame.exists_maj_cart <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open scoped TensorProduct


theorem _root_.GlobalTheory.T.siegelLeviDeterminant_integral_selfDual_lattice : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (v : FinPl D) (p : siegelH (Fv D.host.F v) D.sp.cm.sig (dblSp A).gram), (p : Gv (dblSp A) v) ∈ KFin D.sp.cm.sig (dblSp A).gram L v → ((aH _ D.sp.cm.sig (dblSp A).gram p : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈ intLoc D.host.F D.host.E v := by
  first | exact @GlobalTheory.Core.Rk.AInt.aH_mem_intLoc | exact GlobalTheory.Core.Rk.AInt.aH_mem_intLoc | (intros; apply GlobalTheory.Core.Rk.AInt.aH_mem_intLoc <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.doublingHeightAtRealPlace_le_one : ∀ (D : D7) (A : HSp D) (a : GL (Fin A.rank) (AE D)), IsMaj A a → ∀ (w : InfinitePlace D.host.F) (y : Gw A w), GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW A a w y ≤ 1 := by
  first | exact @GlobalTheory.Core.Rk.HgtArch.hgtW_le_one | exact GlobalTheory.Core.Rk.HgtArch.hgtW_le_one | (intros; apply GlobalTheory.Core.Rk.HgtArch.hgtW_le_one <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.finiteDimensional_thetaFunctions_level_fockDegree : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : RealMat S) (sT : RealMat T), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (U : AddSubgroup (WO S T)), IsOpen (U : Set (WO S T)) → ∀ N : ℕ, FiniteDimensional ℂ (Submodule.span ℂ {f : WO S T → ℂ | IsThetaFunO ψ S T f ∧ (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u f = f) ∧ ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ), l.length = N → l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) f = 0}) := by
  first | exact @GlobalTheory.FockLevelDim.finiteDimensional_level_degree | exact GlobalTheory.FockLevelDim.finiteDimensional_level_degree | (intros; apply GlobalTheory.FockLevelDim.finiteDimensional_level_degree <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_multiplicitySpace_level_of_KFinite_tensors : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (θ : InfFam D), IsInfFam θ → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), (∀ κ ∈ J, κ ∈ GfC V) → ∀ F ∈ MultT θ M ∅ 1, (∀ w ∈ (Submodule.span ℂ {w : SmT M | ∃ v : (M).Vec, (∀ τ, (v τ : (M).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}), ∀ κ ∈ J, ∀ g, F w (g * κ) = χ κ * F w g) → F ∈ MultT θ M J χ := by
  intro D V S M θ hθ J χ hJ F hF hk
  rw [mem_multT, GlobalTheory.MultMem.mem_mult_iff] at hF ⊢
  set T : MMap M := PiTensorProduct.lift.symm F with hTdef
  have hT : ∀ v : M.Vec, T v = F (PiTensorProduct.tprod ℂ v) := fun v => by
    rw [hTdef, PiTensorProduct.lift_symm]; rfl
  refine ⟨hF.aut, hF.cusp, fun v κ hκ g => ?_, hF.equiv, hF.cont⟩
  set U : MMap M := heckeOn M {κ} T - χ κ • T with hUdef
  have hU : U ∈ Mult θ M ∅ 1 :=
    sub_mem ((GlobalTheory.MultMem.mem_mult_iff ..).2 (GlobalTheory.SphericalOps.isMultMap_single hF (hJ κ hκ)))
      (Submodule.smul_mem _ _ ((GlobalTheory.MultMem.mem_mult_iff ..).2 hF))
  have hUv : ∀ (u : M.Vec) (x : GA D V), U u x = T u (x * κ) - χ κ * T u x := fun u x => by
    simp [hUdef, heckeOn, postOn_apply, heckeLin_apply]
  have h0 : U = 0 := GlobalTheory.KFiniteDetermined.restrInj D θ hθ V S M ∅ 1 U hU fun u hu => by
    funext x
    rw [hUv, hT, Pi.zero_apply, sub_eq_zero]
    exact hk _ (Submodule.subset_span ⟨u, fun τ => Submodule.subset_span (hu τ), rfl⟩) κ hκ x
  have := hUv v g
  rw [h0] at this
  exact sub_eq_zero.1 this.symm
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isCompact_finite_adelic_subgroup_integral_open : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ → ∀ K : Subgroup (GA D V), K ≤ GfC V → (∀ k ∈ K, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v) → (∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ K) → IsCompact (K : Set (GA D V)) := by
  first | exact @GlobalTheory.ChainOnto.isCompact_of_integral_open | exact GlobalTheory.ChainOnto.isCompact_of_integral_open | (intros; apply GlobalTheory.ChainOnto.isCompact_of_integral_open <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), Formalism.L2.DIV.IsFrame β Λ → ∀ g : GA D V, Lev.finE V g ∈ Formalism.L2.DIV.St β ↔ ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v := by
  first | exact @GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc | exact GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc | (intros; apply GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.satake_esymm_scaled_multiset_add_segment : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a t k : ℕ) (B : Multiset ℂˣ) (z y : ℂˣ), B.card = a → k ≤ a + t → satEig (qV E w) (a + t) (B.map (z * y⁻¹ * ·) + seg w z t) k = ∑ j ∈ Finset.range (a + 1), (if j ≤ k then (qV E w : ℂ) ^ ((a - j) * (k - j)) * (Formalism.L2.Col.gaussBin (qV E w) t (k - j) : ℂ) * ((z : ℂ) * ((Real.sqrt (qV E w) : ℂ) ^ a)⁻¹) ^ k * (((y : ℂ))⁻¹ * (Real.sqrt (qV E w) : ℂ) ^ (a + t)) ^ j else 0) * satEig (qV E w) a B j := by
  first | exact @GlobalTheory.ChainOnto.satEig_map_add_seg | exact GlobalTheory.ChainOnto.satEig_map_add_seg | (intros; apply GlobalTheory.ChainOnto.satEig_map_add_seg <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.satake_vector_iff_inverse_doubleCosets : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), x ≠ 0 → x ∈ fixed ρ (KGL w (n := n)) → B.card = n → (IsSatVecGL w ρ x B ↔ ∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, heckeVec ρ (KGL w (n := n)) (fun g => Tj ℂ n (Ov E w) ϖ j g⁻¹) x = satEig (qV E w) n (B.map (·⁻¹)) j • x) := by
  first | exact @GlobalTheory.ChainOnto.SatInv.satVec_iff_inv | exact GlobalTheory.ChainOnto.SatInv.satVec_iff_inv | (intros; apply GlobalTheory.ChainOnto.SatInv.satVec_iff_inv <;> assumption)
end
