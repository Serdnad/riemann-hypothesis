module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle025
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle031
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle011
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle052
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle051
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle017
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle059
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle625
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle106
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle635
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle003
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle056
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle057
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle054
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle032
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt

@[expose] public section

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
namespace GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Yd : DivX D}
  {cX : ExtraC}
variable {ex : Extra D L hT Gi Gl K Yd cX}
set_option genInjectivity false in
set_option genSizeOfSpec false in

structure RealInAlt (x : TwIn ex) (Rc : _root_.Formalism.L2.RecTAlt ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) : Type 1 where
  psiPin : x.R.ψ = Rc.T.theta.W.ψ
  hin : ∀ u, Formalism.L2.SG.PoincareInHH.PoincareSetting.InHH S.X u S.Y.hK
  spPin : HEq (x.F.Sp (zsOf x.R x.F)) (Formalism.IndefR.Cx.spOf (X := S.X) (twAt D.what₂.embLL x.A3.A.v0) (x.F.Dc (zsOf x.R x.F)) S.Y.hK S.G
    x.wd (fun m => _root_.Formalism.IndefR.pwOf_alt S hin (x.wd m)) x.bR)
  Sx : Formalism.IndefR.NX.RatDat D.ntw
  nexp : Formalism.IndefR.NX.NExpRealS x.R x.cG Sx
  stdV : ∀ i, (∀ a b, (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b) = if a = b then 1 else 0) ∧
    (Vc D i).L0 = Submodule.span (𝓞 D.host.E) (Set.range (Vc D i).frame)
  stdX : (∀ a b, D.sp.X'.hT (D.sp.X'.frame a) (D.sp.X'.frame b) = if a = b then 1 else 0) ∧
    D.sp.X'.L0 = Submodule.span (𝓞 D.host.E) (Set.range D.sp.X'.frame)
  tS : Formalism.L2.Theta.GA D (Yc D 0)
  cS : ℝ
  κS : ℝ
  ιS : Formalism.L2.Theta.GA D (Yc D 0) ≃* S.X.B.I.GA
  instEq : S.X.B.I = Formalism.IndefR.RationalEmbedding.inst D
  ιS_eq : HEq ιS (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv
  sEEc : Tw (twAt D.what₂.embLL x.A3.A.v0) x.R.HE.H →ₗ⋆[ℂ] Tw (twAt D.what₂.embLL x.A3.A.v0) (Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX S.X)
  sEEj : HEq x.sEE sEEc
  seeLev : (∃ t' : Formalism.L2.Theta.GA D (Yc D 0), Formalism.IndefR.AutomorphicEvaluation.ConjLevel t'⁻¹ (levS _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true))) (Formalism.IndefR.Lev.levChi _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true))) (ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (ιS k))) →
    Formalism.IndefR.AutomorphicEvaluation.ConjLevel tS⁻¹ (levS _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true))) (Formalism.IndefR.Lev.levChi _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true))) (ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (ιS k))
  seeEval : (∃ c' : ℝ, Formalism.IndefR.AutomorphicEvaluation.EvalTieT (x.R.MY 0) x.R.ν0 x.R.fd0 (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) S.X S.G ιS tS c') →
    Formalism.IndefR.AutomorphicEvaluation.EvalTieT (x.R.MY 0) x.R.ν0 x.R.fd0 (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) S.X S.G ιS tS cS
  uS : ℂ
  uS_norm : ‖uS‖ = 1
  seeDef : ∀ (v : Tw (twAt D.what₂.embLL x.A3.A.v0) x.R.HE.H) (hx : x.R.HE.e (Tw.out v) ∈ (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true))),
    sEEc v = Tw.mk (twAt D.what₂.embLL x.A3.A.v0) ((uS * (κS : ℂ)) • (Formalism.IndefR.AutomorphicEvaluation.sEEofTT (x.R.MY 0) x.R.ν0 x.R.fd0 (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) S.X S.G ιS tS cS) ⟨x.R.HE.e (Tw.out v), hx⟩)
  seeK : 0 < κS ∧ ((∃ κ' : ℝ, 0 < κ' ∧ ∀ (v : Tw (twAt D.what₂.embLL x.A3.A.v0) x.R.HE.H) (hx : x.R.HE.e (Tw.out v) ∈ (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true))),
      ‖(κ' : ℂ) • (Formalism.IndefR.AutomorphicEvaluation.sEEofTT (x.R.MY 0) x.R.ν0 x.R.fd0 (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) S.X S.G ιS tS cS) ⟨x.R.HE.e (Tw.out v), hx⟩‖ = ‖v‖) →
    ∀ (v : Tw (twAt D.what₂.embLL x.A3.A.v0) x.R.HE.H), x.R.HE.e (Tw.out v) ∈ (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) →
      RealDat.nP x.F.lv2 true * ‖sEEc v‖ ^ 2 = ‖v‖ ^ 2)
  host : HostHyp D
  vpos : ∀ i, (Vc D i).IsPosDef
variable {x : TwIn ex} {Rc : _root_.Formalism.L2.RecTAlt ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc}

def realisationOfInput (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S) : _root_.Formalism.IndefR.IndefiniteRealisation Rc (divisionPairOfAdelicFormsFaceColumnsData x) x.F.Dc x.F.Sp x.F.Zsc S x.core.Q.c.F where
  Rl := x.R
  sEE := x.sEE
  charW := (x.pins.char)
  zs := rfl
  s0 := (HEq.refl (s0Of x.R x.F))
  s1 := (HEq.refl (s1Of x.R x.F))
  dc := rfl
  sp := HEq.rfl
  col := (HEq.refl (colOf x.R x.F x.sEE))
  allPlaces := x.pins.char.allPl
  trSem := (x.pins.trSem)
  stdChar := x.pins.keep.std
  psiPin := y.psiPin
  signs := (x.pins.keep.signs)
  wdD := x.wd
  wdD_wU := x.wd_wU
  wU_wdD := x.wU_wd
  hin := y.hin
  bR := x.bR
  spPin := (y.spPin)
  frames := fun h => (Formalism.IndefR.Seed.Frm.framesOKg2_iff x.R).2 (x.pins.keep.frames h)
  cG := x.cG
  Sx := y.Sx
  nexp := y.nexp
  stdV := y.stdV
  stdX := y.stdX
  tS := y.tS
  cS := y.cS
  κS := y.κS
  ιS := y.ιS
  instEq := y.instEq
  ιS_eq := y.ιS_eq
  sEEc := y.sEEc
  sEEj := y.sEEj
  seeLev := (y.seeLev)
  seeEval := (y.seeEval)
  uS := y.uS
  uS_norm := y.uS_norm
  seeDef := (y.seeDef)
  seeK := (y.seeK)
  host := y.host
  err_eq := (x.err)
  vpos := y.vpos

def boundedRealisationOfInput (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S) : _root_.Formalism.IndefR.RealTBAlt Rc (divisionPairOfAdelicFormsFaceColumnsData x) x.F.Dc x.F.Sp x.F.Zsc S where
  T := x.core
  Q := _root_.GlobalTheory.Mem.R3.realisationOfInput y
  κ := x.geo.κ
  v₀ := (x.geo.v₀)
  fw := (x.geo.fw)
  bar := (x.geo.bar)
  O := (x.geo.O)
  pins := (x.geo.pins)
  rhoGeo := (x.geo.rhoGeo)
  equivAll := (x.geo.equivAll)
  cTie := (x.geo.cTie)
  phase := by
    have h : ∀ i, x.R.toRealDat.LUnif →
        Formalism.IndefR.FWT.PhaseTie x.core x.R.toRealDat x.geo.κ x.geo.v₀ x.geo.O (phEff x.R) i := by
      rw [phEff_one x]
      exact x.geo.phase
    exact (h)
set_option genInjectivity false in
set_option genSizeOfSpec false in

structure RecursiveInput (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S) : Type 1 where
  E : EigIdx D Yd
  labPi : E.Pi → x.A3.A.fam.base.Ix
  piOf : E.Pi → HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ
  Tp : Formalism.L2.Host.TupTied D x.R.C ex.nch
  tpEq : HEq Tp Rc.T.n.tp
  tupXi : ∀ μ, Formalism.IndefR.RecTie.Used0 D μ → x.R.toLevCh.xiH (x.Y.tupT μ) = Tp.xi μ
  mtRead : Formalism.IndefR.RecTie.MtRead x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj x.Y.IL
    (twPOf (divisionPairOfAdelicFormsFaceColumnsData x) x.Y.tupT x.Y.tupTie)
  mjRead : Formalism.IndefR.RecTie.MjRead x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj x.Y.IL
    (fun i => (x.A3.indefDown (s0Of x.R x.F)).dW i) (fun i v => x.Z.jW i v) ((indefiniteDownJoin (realisationOfInput y)))

def realisationRecursionOfInput {y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S} (r : _root_.GlobalTheory.Mem.R3.RecursiveInput y) : _root_.Formalism.IndefR.IndefiniteRealisationRecursion (_root_.GlobalTheory.Mem.R3.realisationOfInput y) where
  tupT := x.Y.tupT
  hm := x.Y.hm
  hTop := x.Y.hTop
  hinj := x.Y.hinj
  Ish := (x.Y.Ish)
  I0 := (x.Y.Iz)
  IL := (x.Y.IL)
  Kc := x.Y.Kc
  E := r.E
  labPi := r.labPi
  PY := x.Y.PY
  PW := x.Y.PW
  eFT := (x.Y.eFT)
  piOf := r.piOf
  ιW := x.Y.ιW
  Tp := (r.Tp)
  recR := by
    have h : Formalism.IndefR.RecTie.RecReal x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj ex.p0 x.Y.Ish x.Y.Iz x.Y.IL x.Y.Kc r.E
        r.labPi x.Y.PY x.Y.PW x.Y.eFT r.piOf x.Y.ιW ex.nch r.Tp :=
      ⟨x.pins.char.base, x.Y.tied, x.Y.prtE, x.Y.prtE0, x.Y.prtWE, x.Y.xi, r.tupXi,
        fun w => by rw [x.Y.muAt w, x.Y.tupT_tup], x.Y.isomFin, x.Y.frameMatch⟩
    exact (h)
  tpEq := (r.tpEq)
  tupTie := x.Y.tupTie
  tupT_tup := x.Y.tupT_tup
  muEq := (Eq.refl x.R.mu)
  mtRead := (r.mtRead)
  mjRead := (r.mjRead)
end GlobalTheory.Mem.R3
end
end
end

section



section
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option genInjectivity false
set_option genSizeOfSpec false

variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
structure SameGaloisLevel (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (x : St P) : Type 1 where
  a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL (Dof x) (cfOf x) (repOf x.r.Y)
  Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (Dof x).host.E)) → PlE (Dof x).host
  Pq_over : ∀ v, NG.OverPl (Pq v) v
  sel : Set.range Pq = Set.range w.I.sel
structure IntermediateLevel (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (x : St P) : Type 1 extends toLA : _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x where
  mt : InMt x.r.Y (cfOf x) w.I.xi (QOf P)
  rat : InRat x.r.Y x.m.z.cG
  cusp : RowCusp (Dof x) a.A.row
structure FirstIntermediateLevel (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (x : St P) : Type 1 extends toLI : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x where
  b : _root_.GlobalTheory.HeightCounting.SettingsFormsData a rat Pq
structure SecondIntermediateLevel (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (x : St P) : Type 1 extends toLI : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x where
  b : _root_.GlobalTheory.HeightCounting.SeriesData x.m.z.geo a rat mt.ad.PV Pq
structure ThirdIntermediateLevel (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (x : St P) : Type 1 extends toLI : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x where
  b : _root_.GlobalTheory.HeightCounting.ModuliPointsData x.m.z.geo a rat mt.ad.PV Pq
structure StrictHenselianAcyclicLevel (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (x : St P) : Type 1 extends toStrictHenselianAcyclic : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x where
  c : _root_.GlobalTheory.HeightCounting.HeightCountingCharacterData mt b T.k T.psi
variable (hL)
def extensionWithLaw : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL := fun K B f T w Z Wt p0 t nch n xd c => _root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c × PLift (BkLaw (w.D Z))
def SameGaloisLevelExists : Prop := AllSt fun _ _ _ _ _ P x => IsEmpty x.o.N.nd.Loc →
  ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x') ∧ GlobalTheory.TwistChoice.SameGalois (Dof x).nd (Dof x').nd
def RationalityStatementThirdPlaceSeries : Prop := AllSt fun _ _ _ _ _ _ x => _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → Nonempty (InRat x.r.Y x.m.z.cG)
def CuspStatement' : Prop := AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x, RowCusp (Dof x) l.a.A.row
def FirstIntermediateLevelExists : Prop := AllSt fun _ _ _ _ _ P x => _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x → ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.FirstIntermediateLevel hL x')
def SecondIntermediateLevelExists : Prop := AllSt fun _ _ _ _ _ P x => _root_.GlobalTheory.HeightCounting.Up.FirstIntermediateLevel hL x → ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x')
def ThirdIntermediateLevelExists : Prop := AllSt fun _ _ _ _ _ P x => _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x → ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x')
def StrictHenselianAcyclicLevelNonempty : Prop := AllSt fun _ _ _ T _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x, Nonempty (_root_.GlobalTheory.HeightCounting.HeightCountingCharacterData l.mt l.b T.k T.psi)
def EtaStatement' : Prop := AllSt fun _ _ _ _ _ P x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x,
  _root_.GlobalTheory.CoefDuty.AutomorphicSideExists l.a.A l.mt.M l.c.ch l.c.tp.tup → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' =>
    GlobalTheory.CoefDuty.Large D' ∧ ∀ j v, 1 ≤ j → j ≤ (Dof x).R.m → ∀ v' : D'.what₂.places.Pl, HEq v' v → D'.what₂.etaJ j v' = P.q.eta j v
def FinitenessStatement : Prop := AllSt fun K _ _ _ w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (S : SExt) (Γ : GeoP),
  ∃ (Z : w.Lt) (v : Lv3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL) S Γ).s K w Z), v.Wt = P.Wt ∧ Kept l.c.ch v.nch
end GlobalTheory.HeightCounting.Up
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.exists_twOpen_expRel_of_chebSplit : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D' : D7) (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D'), Elem b.D → GlobalTheory.RowTie.ChebSplit b.D.nd → ∃ Tw : TwOpen (withLoc b.L) (chL b.L b.C) (cfL b.L b.cf) (tpL b.L b.tp) (mtL b.L b.M) b.low, ExpRel b.L b.Bs.exp Tw.exp := by
  first | exact @_root_.GlobalTheory.HeightCounting.FitTwExp.exists_twOpen_expRel_alt | exact _root_.GlobalTheory.HeightCounting.FitTwExp.exists_twOpen_expRel_alt | (intros; apply _root_.GlobalTheory.HeightCounting.FitTwExp.exists_twOpen_expRel_alt <;> assumption)
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top
namespace GlobalTheory.Cp
abbrev BaseLevelTiedChoiceAlt (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    {P : Formalism.L2.Rows.RowSideFamily (Fm.ex x hx i) // _root_.Formalism.L2.Rows.RowSideDeterminedAlt ((sel Fm hc).2 x hx h i).T P}
abbrev SelectionDefiniteHeightCondition (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    {p : ℕ × ℕ // (Fm.D x i).s.Del = (p.1 : ℚ) ∧ (Fm.L x i).etaSz = ((Fm.D x i).R.m : ℝ) * (p.2 : ℝ)}
abbrev ColumnChoiceCompatibleSelection (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) (selP : _root_.GlobalTheory.Cp.BaseLevelTiedChoiceAlt 𝒜 sel) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    _root_.GlobalTheory.Cp.SquareIntegrableColumns ((sel Fm hc).2 x hx h i).T (selP Fm hc x hx h i).1
abbrev SelectionSpectralCondition (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt ((sel Fm hc).2 x hx h i)
def IndefiniteScaleAtPoint {𝒜 : FamClass} (sel : _root_.Formalism.L2.TwistSelection 𝒜) (selP : _root_.GlobalTheory.Cp.BaseLevelTiedChoiceAlt 𝒜 sel) (selDH : _root_.GlobalTheory.Cp.SelectionDefiniteHeightCondition 𝒜 sel) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm)
    (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x) :
    Formalism.L2.Indef.DefSub (selP Fm hc x hx h i).1.A3.fam3.amb3 → Formalism.L2.Indef.IndefScale (selP Fm hc x hx h i).1.A3.fam3.base3 :=
  fun Zs =>
    let z := Formalism.L2.DIV.ZscOfNum3 (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0
      (Formalism.L2.DIV.ofRecord (Fm.D x i) (Fm.L x i) (selDH Fm hc x hx h i).1.1 (selDH Fm hc x hx h i).1.2) (Equiv.refl _) (Fm.L x i).Nc Zs
    { z with l6m := fun j => z.l6m j - Fm.Csz * z.l6u, l6u := 0 }
abbrev SelectionBundle (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) (selS : _root_.GlobalTheory.Cp.SelectionSpectralCondition 𝒜 sel) (selP : _root_.GlobalTheory.Cp.BaseLevelTiedChoiceAlt 𝒜 sel) (selDH : _root_.GlobalTheory.Cp.SelectionDefiniteHeightCondition 𝒜 sel) (selC : _root_.GlobalTheory.Cp.ColumnChoiceCompatibleSelection 𝒜 sel selP) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    _root_.Formalism.IndefR.RealTBAlt ((sel Fm hc).2 x hx h i) (selP Fm hc x hx h i).1 (selC Fm hc x hx h i).c.face (selC Fm hc x hx h i).Sp
      (_root_.GlobalTheory.Cp.IndefiniteScaleAtPoint sel selP selDH Fm hc x hx h i) (selS Fm hc x hx h i)
def EventuallyAlongSelection {𝒜 : FamClass} (sel : _root_.Formalism.L2.TwistSelection 𝒜) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm)
    (Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x), Prop) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x), x0 ≤ x → ∀ i : Fm.Ix x, Q x hx h i
end GlobalTheory.Cp
namespace GlobalTheory.Fc
open GlobalTheory.Cp
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure BundleCondition (D : D7) (O : Obj D) (c : ℝ) : Type 1 where
  R : _root_.Formalism.L2.RecTAlt O.ex
  S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R
  P : Formalism.L2.Rows.RowSideFamily O.ex
  pin : _root_.Formalism.L2.Rows.RowSideDeterminedAlt R.T P
  DH : {p : ℕ × ℕ // D.s.Del = (p.1 : ℚ) ∧ O.L.etaSz = (D.R.m : ℝ) * (p.2 : ℝ)}
  C : _root_.GlobalTheory.Cp.SquareIntegrableColumns R.T P
  B : _root_.Formalism.IndefR.RealTBAlt R P C.c.face C.Sp (zsc P DH.1.1 DH.1.2 c) S
variable {𝒜 : FamClass} (σ : RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜)
def familySelection : _root_.Formalism.L2.TwistSelection 𝒜 := fun Fm hc => ⟨Fm.x1, fun x hx _ i => (σ Fm hc x hx i).R⟩
def spectralConditionOfRawSelection : _root_.GlobalTheory.Cp.SelectionSpectralCondition 𝒜 (_root_.GlobalTheory.Fc.familySelection σ) := fun Fm hc x hx _ i => (σ Fm hc x hx i).S
def baseLevelChoiceOfRawSelection : _root_.GlobalTheory.Cp.BaseLevelTiedChoiceAlt 𝒜 (_root_.GlobalTheory.Fc.familySelection σ) := fun Fm hc x hx _ i => ⟨(σ Fm hc x hx i).P, (σ Fm hc x hx i).pin⟩
def definiteHeightOfRawSelection : _root_.GlobalTheory.Cp.SelectionDefiniteHeightCondition 𝒜 (_root_.GlobalTheory.Fc.familySelection σ) := fun Fm hc x hx _ i => (σ Fm hc x hx i).DH
def columnChoiceOfRawSelection : _root_.GlobalTheory.Cp.ColumnChoiceCompatibleSelection 𝒜 (_root_.GlobalTheory.Fc.familySelection σ) (_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection σ) := fun Fm hc x hx _ i => (σ Fm hc x hx i).C
def selectionBundleOfRawSelection : _root_.GlobalTheory.Cp.SelectionBundle 𝒜 (_root_.GlobalTheory.Fc.familySelection σ) (_root_.GlobalTheory.Fc.spectralConditionOfRawSelection σ) (_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection σ) (_root_.GlobalTheory.Fc.definiteHeightOfRawSelection σ) (_root_.GlobalTheory.Fc.columnChoiceOfRawSelection σ) := fun Fm hc x hx _ i => (σ Fm hc x hx i).B
end GlobalTheory.Fc
end
end
end

section



section
noncomputable section
open scoped InnerProductSpace
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx
  Formalism.IndefR.Links Formalism.L2.SG.PackageTie2 Formalism.L2.SG.KerJoinS Formalism.IndefR.CxPass
namespace GlobalTheory.MiS
open _root_.Formalism Formalism.IndefR Formalism.IndefR.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC}
structure RealPackAlt (ex : Extra D L hT Gi Gl Kc Yd cX) where
  R : _root_.Formalism.L2.RecTAlt ex
  S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R
  P : RowSideFamily ex
  Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)
  Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)
  Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3
  Ks : Type
  [fKs : Field Ks]
  [nKs : NumberField Ks]
  [aKs : Algebra Ks D.what₂.LL]
  Q : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks
attribute [instance] _root_.GlobalTheory.MiS.RealPackAlt.fKs _root_.GlobalTheory.MiS.RealPackAlt.nKs _root_.GlobalTheory.MiS.RealPackAlt.aKs
variable {ex : Extra D L hT Gi Gl Kc Yd cX}
def HypothesisAtPackage (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Prop :=
  Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin W.R W.S W.Q) ∧
    (∀ u, Formalism.L2.SG.ColDict.LevelMatch W.S.X (W.S.tr u) W.S.Y.hK) ∧ DcPtG W.P ∧ W.Q.Rl.Char3 W.Q.F ∧ FramesOKg2 W.Q.Rl
abbrev packageCoefficientSpace (W : _root_.GlobalTheory.MiS.RealPackAlt ex) := W.Q.Rl.toCx3 W.Q.F
def LevelHypothesis (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Prop :=
  (∃ s, W.P.A3.fam3.Ok3 s) ∧ (_root_.GlobalTheory.MiS.packageCoefficientSpace W).RatZ ∧
    ∃ gE : Representation ℂ W.P.Gp (_root_.GlobalTheory.MiS.packageCoefficientSpace W).EE, GUnit3 (_root_.GlobalTheory.MiS.packageCoefficientSpace W) gE ∧ GEquiv3 W.P.A3 (_root_.GlobalTheory.MiS.packageCoefficientSpace W) gE ∧
      PrincipalLevelBijectivity W.P.A3 (_root_.GlobalTheory.MiS.packageCoefficientSpace W) (P1 := W.P.Ps) (ψ1 := W.P.ψs) (Dc := W.Dcf) (Sp := W.Spf) (Zsc := W.Zscf) ∧
      LevType3 W.P.A3 (_root_.GlobalTheory.MiS.packageCoefficientSpace W) (P1 := W.P.Ps) (ψ1 := W.P.ψs) (Dc := W.Dcf) (Sp := W.Spf) (Zsc := W.Zscf) gE false W.P.P0 W.P.ψ0 ∧
      LevType3 W.P.A3 (_root_.GlobalTheory.MiS.packageCoefficientSpace W) (P1 := W.P.Ps) (ψ1 := W.P.ψs) (Dc := W.Dcf) (Sp := W.Spf) (Zsc := W.Zscf) gE true W.P.Ps W.P.ψs
end GlobalTheory.MiS
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.RowPlacementReal
theorem placement_of_realisation_alt : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks), _root_.Formalism.IndefR.IndefiniteRealisationNormalisation Q → (∀ x : S.X.B.I.E, HEq (S.X.ιE x) x) → _root_.Formalism.IndefR.IndefiniteRealisationExtends Q := by
  intro hDS D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S Ks _ _ _ Q hP hE
  have hE0 : Formalism.L2.SG.RowDict.IdempotentRealFixed D := by
    have key : ∀ {g : ℕ} [Fact g.Prime] {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod g)} (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) C), Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O → ∀ (r : ℕ) (f : Polynomial (ZMod g)), f.Monic → f.coeff 0 ≠ 0 → ∀ x, star ((Formalism.L2.NT.eSerO O r f).coeff x) = (Formalism.L2.NT.eSerO O r (Polynomial.C (f.coeff 0)⁻¹ * f.reverse)).coeff x := GlobalTheory.T.star_coeff_eisenstein_series_reverse_poly
    exact GlobalTheory.GoodIdemReal.star_coeff_of_reverse D (fun k f hm h0 x => by
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      rw [Rc.T.n.types.eSer_def, Rc.T.n.types.eSer_def]
      exact key _ (Rc.T.n.types.O_equiv k) D.R.r f hm h0 x)
  exact GlobalTheory.T.exists_rowPlacement_finiteElement_matches_levels hDS Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 S.X S.G Q.instEq Q.ιS Q.tS Q.cG
    Q.charW.base.lev Q.charW.base.grp Q.charW.base.models Q.host hE0 Q.ιS_eq hE hP.grpRecPin hP.tSfin hP.tSpin
end GlobalTheory.RowPlacementReal
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PrimIn
theorem rowTest_setting_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S), _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q → (∀ w, (B.Q.Rl.toCx3 B.Q.F).W1 B.Q.F.cr (B.Q.Rl.num B.Q.F 0 0) w → w ∈ B.Q.Rl.twPl) → B.Q.Rl.toRealDat.ExAt → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L → GlobalTheory.GLq.ESerTie D → Finite P.T → GlobalTheory.RowClaim.HidaSetting L B.Q.Rl.toRealDat B.Q.F.lv2 := by
  intro D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S B hp _hW hEx hsz hser hfin
  have hC := B.Q.charW
  have hcore := (GlobalTheory.CoreOfWeak.core_of_weak B.Q.Rl B.Q.F hC hEx).1
  exact
    { size := hsz
      eser := hser
      host := B.Q.host
      hF := hp.hF
      core := hcore
      mu_off := hC.tup.mu_off
      mu_used := hC.tup.mu_used
      mu_ne := hC.tup.mu_ne
      mu_conj := hC.tup.mu_conj
      mu_on := hC.tup.mu_on
      grp := hC.base.grp.record
      guard := hp.qGuard
      fin := hfin
      fullY := hC.fullY
      fullX := hC.fullX
      std := B.Q.stdChar
      stdX := B.Q.stdX
      betaX := hp.betaStd.2 }
end GlobalTheory.PrimIn
end
end

section



section
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
structure ParityConditions (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (Rw : RowSide D) : Type 1 where
  T : GlobalTheory.RowTie.WDTie D.nd D.naut
  lab : LabTrue D T
  chr : CharSide D cf
  cg : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T
  A : _root_.GlobalTheory.HeightCounting.AUSideAlt D
  au : _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL D T A
  row : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (Rw.locR σ w)) Rw.satR
def ParityConditions.ofSt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {cf : CharFrame D} {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}
    (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf rep) : _root_.GlobalTheory.HeightCounting.Up.ParityConditions hL D cf rep a.A.row := ⟨a.A.wdT, a.A.lab, a.A.chr, a.cg, a.A.au, a.au, a.row⟩
structure ParityLaws (D : D7) : Prop where
  tie0 : SumRepresentations.tie0 D
  an : SumRepresentations.adm5 D
  temp : _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D
  lab : SumRepresentations.tieLab D
  one : GlobalTheory.RowCopy.HeckeSplitOne D
  cancel : ∀ w (a b c : D.naut.LP w), D.naut.lpSum a c = D.naut.lpSum b c → a = b
  gsp : ∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v)
end GlobalTheory.HeightCounting.Up
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx NumberField

theorem _root_.GlobalTheory.T.V0_map_iota_eq_top_real_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) (_ : Field Ks) (_ : NumberField Ks) (_ : Algebra Ks D.what₂.LL) (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (s : ℕ), P.A3.fam3.Ok3 s → P.A3.fam3.TypesSep3 → PrimRows3 Q.Rl Q.F → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  first | exact @_root_.GlobalTheory.V0_map_iota_eq_top_of_real_alt | exact _root_.GlobalTheory.V0_map_iota_eq_top_of_real_alt | (intros; apply _root_.GlobalTheory.V0_map_iota_eq_top_of_real_alt <;> assumption)
end
end
