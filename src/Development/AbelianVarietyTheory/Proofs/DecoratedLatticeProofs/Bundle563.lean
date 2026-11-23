module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle025
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartW
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle008
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle562
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle184
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle161
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle398
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle242
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle273
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle241
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle243
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle385
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle492
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle321
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle520
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumDescendsToWittCore
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seeSaw_latticeFramePins_finiteIntegralLaws : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι) (n : ℕ) (G : Fin n → GLoc v), c.Is → c.VolLast → v.Is → ShapeOff v o → GPin G → ∃ (ε : ℕ → ι → 𝓀[k]ˣ) (op : ∀ j, BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) (r : ℕ → ι → ℝ) (e : ℕ → ι → ℤ) (a : ℕ → ℂ), (∀ j i, 0 < r j i) ∧ (∀ j, a j ≠ 0) ∧ (∀ j σ h, v.kap j σ h ≠ 0) ∧ ((v.withT (o.S ε) op).withCG a).Is ∧ ∀ (𝒯 : Type) (t : 𝒯 → Tup c) (w : ∀ s, VTup (t s)), (∀ s, (t s).Is ∧ VForm ((v.withT (o.S ε) op).withCG a) (w s) ∧ WeilOK (t := t s) v ∧ TopSph (t := t s) v ∧ (t s).UnrOn (offP v (w s)) ∧ (t s).UnrK (· ∈ v.tP) ∧ (∀ i, (G i).Chars (t s)) ∧ QLaw v (w s) ∧ QLast v (w s) ∧ QFin v (w s) ∧ (∀ j ρ h, (w s).cT j = o.mono (r j) (e j) ((t s).sBF j ρ h).χW) ∧ CVEq ((v.withT (o.S ε) op).withCG a) (w s)) → (∀ s, (t s).LocFin) ∧ ValX t ∧ ValLastX t := by
  first | exact @GlobalTheory.SeeSaw.pins_finiteIntegrals | exact GlobalTheory.SeeSaw.pins_finiteIntegrals | (intros; apply GlobalTheory.SeeSaw.pins_finiteIntegrals <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seeSawTwistPlaceLaws_of_rootOfUnityRescaling : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → t.Is → v.Is → WeilOK (t := t) v → QPinU v w → QLaw v w ∧ QLast v w ∧ QFin v w := by
  first | exact @GlobalTheory.QTw.laws_of_pin_resc | exact GlobalTheory.QTw.laws_of_pin_resc | (intros; apply GlobalTheory.QTw.laws_of_pin_resc <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem GlobalTheory.Unf.iteratedUnfolding_of_descent : ∀ D : D7, Descent D → IT D :=
  fun D hD => GlobalTheory.T.iteratedThetaUnfolding_of_doubleStep_lastTwoSteps D (GlobalTheory.T.besselPeriod_double_step_unfolding_of_descent D hD) (GlobalTheory.T.doubleLiftPeriod_rankZero_fubini_compactQuotient D)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem mainX_of_lawsX (hR : GlobalTheory.Published.CuspRapidDecay) (hH : GlobalTheory.Published.HarishChandraModules) :
    ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), LawsX t → MainX t := by
  intro D c 𝒯 t L
  have hTwo : TwoX t :=
    GlobalTheory.T.seeSawDoubleLiftCombination_of_laws D c 𝒯 t (GlobalTheory.T.seeSawWeilBiAction_commutes D) (GlobalTheory.T.centralEigenTheta_isFockVector_bounded_degree D) (GlobalTheory.SeeSaw.LiftSumProof.liftSum D)
      L.com L.tup L.real L.ker L.rd
  have hRap : RapidVal D := GlobalTheory.SeeSaw.rapidVal_of_cuspRapidDecay hR D
  have hStep : StepX t :=
    GlobalTheory.T.seeSaw_doubleStep_linearRelations_periods hH D c 𝒯 t (GlobalTheory.T.besselPeriod_double_step_unfolding_of_descent D (GlobalTheory.Desc.weil_data_descend D)) hRap
      (GlobalTheory.ValMoveProof.valMove D) (GlobalTheory.SeeSaw.perSum_all D) L.com L.tup L.loc L.val hTwo L.rd
  have hLast : LastX t :=
    GlobalTheory.T.seeSaw_lastTwoSteps_transport_linear_relations hH D c 𝒯 t hRap L.com L.tup L.last hTwo L.per L.rd
  exact GlobalTheory.SeeSaw.mainX_of_stepX_lastX D c 𝒯 t L.tup hStep hLast

end GlobalTheory.SeeSaw
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaLift_scalarIdentity_matching_adjointInjective : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilSiegelFormulaUnitary → (∀ D' : Formalism.BasicNotions.D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D') → GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → D.host.ccK = ⊤ → R.Sb = R.Pg → (∀ t P, GlobalTheory.Hk3.Good R t P → Formalism.DivisionValues.conjPl P = P → GlobalTheory.Hk3.FixAll R t P) → ∀ SF, GlobalTheory.Hk3.IsSF R SF → GlobalTheory.TrCopy.TRLev R F SF → Scal R SF ∧ MatchUp R SF ∧ UpInj R ∧ UpInjW R := by
  first | exact @GlobalTheory.ScalAll.scal_matchUp_upInj | exact GlobalTheory.ScalAll.scal_matchUp_upInj | (intros; apply GlobalTheory.ScalAll.scal_matchUp_upInj <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

theorem _root_.GlobalTheory.T.thetaLift_theoremA_publishedHypotheses : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilSiegelFormulaUnitary → (∀ D' : Formalism.BasicNotions.D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D') → GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → HostHyp D → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → D.host.ccK = ⊤ → FWT.QGuard R.toRealDat → GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R.toRealDat → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → R.PThmA := by
  first | exact @GlobalTheory.ThmAFinal.pThmA_short | exact GlobalTheory.ThmAFinal.pThmA_short | (intros; apply GlobalTheory.ThmAFinal.pThmA_short <;> assumption)
end
