module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle030
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeakCharInertPartRealAdelicDataTransport
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle259
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
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
public import Lean.Meta.Injective
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle013
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle010
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle023
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
public import Formalism.LocalToGlobal.Divisibility.ColumnFamilyPlaceCharacterComap
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Yd : DivX D}
  {cX : ExtraC}


set_option genInjectivity false in
set_option genSizeOfSpec false in

structure TwIn (ex : Extra D L hT Gi Gl K Yd cX) : Type 1 where
  G : Type
  [grp : Group G]
  [fin : Fintype G]
  Pl0 : Type
  I0 : Type
  T : Type
  A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m
  core : Formalism.L2.Pj.CoreJ D
  [alg : Algebra core.Q.c.F D.what₂.LL]
  R : RealDat3 D A3 core.Q.c.F
  F : Face3 D A3
  cG : G0 R.Pg D.R.r ≃* G0g D.nd
  geo : GlobalTheory.RealGeo.GeoHalf core R.toRealDat fun _ => 1
  pins : Pins R F cG
  err : ErrEq R F
  Y : Read (A3 := A3) R.toRealDat F.lv2 ex.p0
  Z : ReadL R F ex.p0 Y
  C : ReadC R F ex.p0 Y
  sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH
  div : DivDef3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (zsOf R F) (s0Of R F) (s1Of R F) ex.p0 (colOf R F sEE) C.NuC (idsOf cG Z C)
  JA : AmbIds D A3.A ex.p0.s ex.amb0 F.P0 F.ψ0 Y.tup
  amb0 : AmbTie D A3.A ex.p0.s ex.amb0 F.P0 F.ψ0 Y.tup Y.jA0 JA
  JM : MjHIds D A3.A Yd (A3.indefDown (s0Of R F))
  mjH : MjHTie D A3.A Yd (A3.indefDown (s0Of R F)) Z.jW JM

attribute [instance] TwIn.grp TwIn.fin TwIn.alg

variable {ex : Extra D L hT Gi Gl K Yd cX}



@[reducible] def divisionPairOfAdelicFormsFaceColumnsData (x : TwIn ex) : RowSideFamily ex where
  Gp := x.G
  Pl0 := x.Pl0
  I0 := x.I0
  T := x.T
  A3 := x.A3
  P0 := x.F.P0
  ψ0 := x.F.ψ0
  Ps := x.F.P1
  ψs := x.F.ψ1
  Zs := zsOf x.R x.F
  S0 := s0Of x.R x.F
  S1 := s1Of x.R x.F
  Dc := x.F.Dc (zsOf x.R x.F)
  Sp := x.F.Sp (zsOf x.R x.F)
  C := colOf x.R x.F x.sEE
  NuC := x.C.NuC
  I := idsOf x.cG x.Z x.C
  JA := x.JA
  JM := x.JM
  tied := ⟨x.div, x.amb0, x.mjH, x.Y.cen0 x.cG x.pins.keep⟩

def TwIn.wd (x : TwIn ex) : (x.F.Dc (zsOf x.R x.F)).Mem → D.what₂.Word := (Equiv.ofBijective _ x.C.bij).symm

theorem TwIn.wd_wU (x : TwIn ex) (u : D.what₂.Word) : x.wd (x.C.wU u) = u := (Equiv.ofBijective _ x.C.bij).symm_apply_apply u

theorem TwIn.wU_wd (x : TwIn ex) (m : (x.F.Dc (zsOf x.R x.F)).Mem) : x.C.wU (x.wd m) = m :=
  (Equiv.ofBijective _ x.C.bij).apply_symm_apply m

def TwIn.bR (x : TwIn ex) (m : (x.F.Dc (zsOf x.R x.F)).Mem) (i : Fin ((x.F.Dc (zsOf x.R x.F)).a m)) : (D.mem (x.wd m)).A.Mram :=
  D.eMu (x.wd m) (D.jN (x.wd m) (x.C.eNu (x.wd m)
    (Pi.single (Fin.cast (congrArg (x.F.Dc (zsOf x.R x.F)).a (x.wU_wd m)).symm i) 1)))


set_option genInjectivity false in
set_option genSizeOfSpec false in

structure RealIn (x : TwIn ex) (Rc : Formalism.L2.RecT ex) (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) : Type 1 where
  psiPin : x.R.ψ = Rc.T.theta.W.ψ
  hin : ∀ u, Formalism.L2.SG.PoincareInHH.PoincareSetting.InHH S.X u S.Y.hK
  spPin : HEq (x.F.Sp (zsOf x.R x.F)) (Formalism.IndefR.Cx.spOf (X := S.X) (twAt D.what₂.embLL x.A3.A.v0) (x.F.Dc (zsOf x.R x.F)) S.Y.hK S.G
    x.wd (fun m => pwOf S hin (x.wd m)) x.bR)
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

variable {x : TwIn ex} {Rc : Formalism.L2.RecT ex} {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc}


theorem phEff_one (x : TwIn ex) : phEff x.R = fun _ => 1 := by
  funext i
  unfold phEff
  rw [x.pins.phs i]
  simp




end GlobalTheory.Mem.R3

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host
open Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.RealGeo
open scoped TensorProduct

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B}

structure Refill (a : Late B C) where

  S : SStage B C a.W

  G : GJStage B C

  L : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V

  h : B.Word → ℝ

  HH : ℝ

  HH_ge : sFrame (fun u => { a.V.div.Nu u with L := L u }) h + a.V.div.RR.muMax ≤ HH

  etaF : ℝ

abbrev Refill.to {a : Late B C} (c : Refill a) : Late B C :=
  ⟨a.W, { a.V with
      div := { a.V.div with Nu := fun u => { a.V.div.Nu u with L := c.L u }, h := c.h, HH := c.HH, HH_ge := c.HH_ge, etaF := c.etaF } },
    c.S, a.N, c.G⟩

abbrev Refill.ofSG (a : Late B C) (S : SStage B C a.W) (G : GJStage B C) : Refill a :=
  ⟨S, G, fun u => (a.V.div.Nu u).L, a.V.div.h, a.V.div.HH, a.V.div.HH_ge, a.V.div.etaF⟩

abbrev Refill.ofDiv (a : Late B C) (L : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V) (h : B.Word → ℝ) : Refill a :=
  ⟨a.S, a.G, L, h, max 1 (sFrame (fun u => { a.V.div.Nu u with L := L u }) h + a.V.div.RR.muMax), le_max_right _ _, a.V.div.etaF⟩

def Refill.same {a : Late B C} (c : Refill a) : SameGrp a c.to := SameGrp.ofN a.N a.V c.to.V a.S c.S a.G c.G

def Refill.same' {a : Late B C} (c : Refill a) : SameGrp c.to a := SameGrp.ofN a.N c.to.V a.V c.S a.S c.G a.G

namespace Tr

variable {a : Late B C} (c : Refill a) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

def rowSide {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (X : RowSide a.D EE) :
    RowSide c.to.D EE where
  Amb := (X.Amb)
  instAmb := (X.instAmb)
  instAmbi := (X.instAmbi)
  instAmbf := (X.instAmbf)
  Mult := (X.Mult)
  instMult := (X.instMult)
  instMulti := (X.instMulti)
  instMultf := (X.instMultf)
  multZero := (X.multZero)
  multTop := (X.multTop)
  io := (X.io)
  Mtilde := (X.Mtilde)
  cen := (X.cen)
  eOp := (X.eOp)
  eOp_idem := (X.eOp_idem)
  eOp_sa := (X.eOp_sa)
  eOp_tie := (X.eOp_tie)
  RR := (X.RR)
  RR_frames := (X.RR_frames)
  jEE := (X.jEE)
  jEE_basis := (X.jEE_basis)
  jEE_norm := (X.jEE_norm)

def baseLevelRowSideTransport (X : BaseLevelRowSide a.D) : BaseLevelRowSide c.to.D := ⟨(@rowSide B C a c (@Rows.Data.EE0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0i (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0f (@Late.D B C a).R (@Late.D B C a).what₂) (@BaseLevelRowSide.s (@Late.D B C a) X))⟩

def colReal (K : ColReal a.D) : ColReal c.to.D := ⟨(K.xi)⟩

section Chain

variable {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} {R : RealDat a.D A Ks} {F : Face a.D A} {tupT : a.D.what₂.Tup → T}
  {hm : 0 < a.D.R.m} {hTop : TopMultH R}


variable (F tupT hm hTop) in
def spEEc : type_of% (toChainReal R F tupT hm hTop).EEc := ((chainB c.to F tupT hm hTop).EEc)


variable (F tupT hm hTop) in
theorem spEEc_eq : (toChainReal R F tupT hm hTop).EEc = spEEc c F tupT hm hTop := (chain_EEc c.to F tupT hm hTop)


variable (F tupT hm hTop) in
def spCC : type_of% (toChainReal R F tupT hm hTop).CC := ((chainB c.to F tupT hm hTop).CC)


variable (F tupT hm hTop) in
theorem spCC_eq : (toChainReal R F tupT hm hTop).CC = spCC c F tupT hm hTop := (chain_CC c.to F tupT hm hTop)


variable (F tupT hm hTop) in
def spCCP : type_of% (toChainReal R F tupT hm hTop).CCP := ((chainB c.to F tupT hm hTop).CCP)


variable (F tupT hm hTop) in
theorem spCCP_eq : (toChainReal R F tupT hm hTop).CCP = spCCP c F tupT hm hTop := (chain_CCP c.to F tupT hm hTop)


variable (F tupT hm hTop) in
def spCCX : type_of% (toChainReal R F tupT hm hTop).CCX := ((chainB c.to F tupT hm hTop).CCX)


variable (F tupT hm hTop) in
theorem spCCX_eq : (toChainReal R F tupT hm hTop).CCX = spCCX c F tupT hm hTop := (chain_CCX c.to F tupT hm hTop)


variable (F tupT hm hTop) in
def spCCXP : type_of% (toChainReal R F tupT hm hTop).CCXP := ((chainB c.to F tupT hm hTop).CCXP)


variable (F tupT hm hTop) in
theorem spCCXP_eq : (toChainReal R F tupT hm hTop).CCXP = spCCXP c F tupT hm hTop := (chain_CCXP c.to F tupT hm hTop)


variable (F tupT hm hTop) in
def okB (l : Bool) (μ : a.D.what₂.Tup) : Prop := (chainB c.to F tupT hm hTop).IoOK l ((μ))

theorem okB_imp {l : Bool} {μ : a.D.what₂.Tup} (h : okB c F tupT hm hTop l μ) : (toChainReal R F tupT hm hTop).IoOK l μ :=
  chain_ioOK c.to F tupT hm hTop ((h))

def ioCB (l : Bool) (μ : a.D.what₂.Tup) (k : ℕ) (v : (toChainReal R F tupT hm hTop).CC l μ (k + 1)) : (toChainReal R F tupT hm hTop).Amb k :=
  (by with_unfolding_all exact (((chainB c.to F tupT hm hTop).ioC l ((by with_unfolding_all exact (μ :))) k
    ((by with_unfolding_all exact ((LinearEquiv.ofEq _ _ (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) (k + 1)) v) :)))).1 :))

theorem ioCB_eq (l : Bool) (μ : a.D.what₂.Tup) (k : ℕ) (v : (toChainReal R F tupT hm hTop).CC l μ (k + 1)) :
    ioCB c l μ k v = ((toChainReal R F tupT hm hTop).ioC l μ k v).1 :=
  (by with_unfolding_all exact ((chain_ioC c.to (R := R) (tupT μ) k ((v.1))
    (((LinearEquiv.ofEq _ _ (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) (k + 1)) v).2)) ((v.2))) : _))

def ioXB' (l : Bool) (μ : a.D.what₂.Tup) (v : (toChainReal R F tupT hm hTop).CCX l μ) : (toChainReal R F tupT hm hTop).Amb (a.D.R.m - 1) :=
  (by with_unfolding_all exact (((chainB c.to F tupT hm hTop).ioX l ((by with_unfolding_all exact (μ :))) ((by with_unfolding_all exact ((LinearEquiv.ofEq _ _ (congrFun (congrFun (spCCX_eq c F tupT hm hTop) l) μ) v) :)))).1 :))

theorem ioXB'_eq (l : Bool) (μ : a.D.what₂.Tup) (v : (toChainReal R F tupT hm hTop).CCX l μ) :
    ioXB' c l μ v = ((toChainReal R F tupT hm hTop).ioX l μ v).1 :=
  (by with_unfolding_all exact ((chain_ioX c.to (R := R) hm hTop (tupT μ) ((by with_unfolding_all exact (v.1 :))) ((by with_unfolding_all exact ((topMult_tr c.to hTop) :)))
    ((by with_unfolding_all exact ((LinearEquiv.ofEq _ _ (congrFun (congrFun (spCCX_eq c F tupT hm hTop) l) μ) v).2 :))) ((by with_unfolding_all exact (v.2 :)))) :))

end Chain

end Tr

end GlobalTheory.Mem.R3

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Res

section Geo

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {ph : Fin D.R.m → ℂ}



def geoScal (g : GlobalTheory.RealGeo.GeoHalf C R ph) (kap lam err) :
    GlobalTheory.RealGeo.GeoHalf C ({ R.upd6 kap lam with err0 := err } : RealDat D A C.Q.c.F) ph :=
  ⟨g.κ, g.v₀, GlobalTheory.RealGeo.Upd.updFWT C R kap lam err g.fw, g.bar, fun i => GlobalTheory.RealGeo.Upd.updO C R kap lam err (g.O i),
    fun i => GlobalTheory.RealGeo.Upd.omPins_upE kap lam err g.O i (g.pins i), g.rhoGeo, g.equivAll, g.cTie, g.phase⟩


end Geo

section Generic

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T T' : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]




def KapFixed (S : RealDat3 D A3 Ks) (κ : ℝ) : Prop :=
  Lift.IsKap D.R.m (fun t => S.Th t ∘ₗ LinearMap.adjoint (S.Th t)) S.EEp3 S.lamN κ ∧
    ∃ t p, S.EEp3 p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, S.lamN t j p ≠ 0


open Classical in
def kapNew (S : RealDat3 D A3 Ks) : ℝ := if h : ∃ κ, KapFixed S κ then h.choose else S.kap

theorem kapNew_eq (S : RealDat3 D A3 Ks) {κ : ℝ} (h : KapFixed S κ) : kapNew S = κ := by
  have h' : ∃ κ, KapFixed S κ := ⟨κ, h⟩
  unfold kapNew
  rw [dite_eq_left h']
  obtain ⟨t, p, hp, hl⟩ := h.2
  exact Lift.IsKap.unique h'.choose_spec.1 h.1 t p hp hl

theorem kapNew_of_not (S : RealDat3 D A3 Ks) (h : ¬ ∃ κ, KapFixed S κ) : kapNew S = S.kap := dif_neg h

theorem kapNew_of_scal (S : RealDat3 D A3 Ks) (h : S.scal_kap) : kapNew S = S.kap := by
  by_cases h' : ∃ κ, KapFixed S κ
  · obtain ⟨κ, hκ⟩ := h'
    exact (kapNew_eq S hκ).trans (h κ hκ.1 hκ.2).symm
  · exact kapNew_of_not S h'


variable {f : T' → T} {μ : T'} {R : RealDat3 D (A3.comap id (f μ)) Ks} {mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T'}
  {tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))} {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {P1 : Subgroup G} {ψ1 : P1 →* D.what₂.LLˣ}



end Generic

end Res

section Record

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
  {Wt Wt' : Set X.B.places.Pl} (z : Dat X I hX T Wt)

namespace Dat








end Dat

end Record

end GlobalTheory.Mem.R3

end
end
