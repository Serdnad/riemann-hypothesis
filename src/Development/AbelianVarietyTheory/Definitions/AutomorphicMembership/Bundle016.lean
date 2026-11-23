module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Formalism.LocalToGlobal.HermitianForms.TiedTwSymAll
public import Formalism.LocalToGlobal.KernelLattices.Bundle004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RefilledStagesRecord
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
public import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle001

@[expose] public section

section

noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.L2.Host GlobalTheory.CuspRep NumberField IsDedekindDomain

structure CGTrue (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) where
  e : ∀ a, D.naut.CG a ↪ HostCGu D.host a
  surj : ∀ a, 0 < a → Function.Surjective (e a)
  zero : IsEmpty (D.naut.CG 0)
  loc : ∀ a (π : D.naut.CG a) w, T.e w (D.naut.locG π w) = ParLaws.locG hL D.nd.plOm (e a π) w
  tw : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a) (χ : D.naut.CG 1), e a (D.naut.tw π χ) = (e a π).tw (e 1 χ)
  inf : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a) τ, D.naut.infG π τ = (e a π).infChar τ
  csd : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a), D.naut.csd π ↔ (e a π).IsCsd

def wdCG {D : D7} (hE : IsEmpty D.nd.Loc) (K : CGK D.naut) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) :
    GlobalTheory.RowTie.WDTie (setCG D hE K).nd (setCG D hE K).naut := { T with }

def cfCG {D : D7} (hE : IsEmpty D.nd.Loc) (K : CGK D.naut) (c : CharFrame D) : CharFrame (setCG D hE K) :=
  ⟨c.P, c.W, c.mu0, c.eta, c.chiPsi, c.del, c.del', c.isMu0, c.isEta, c.isChi, c.isDel, c.isDel'⟩

end GlobalTheory.HeightCounting

end
end

section

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Chr Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

def TopPt (u : B.Word) (a : I.ι) (k : GA B (B.R.N B.R.m)) : Prop :=
  ∀ (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)), PtOf g' d →
    IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1 →
    PtOf (g * k) (tilF I.sel (I.tup a) u d)


section Tw

variable (l0 : I.Law0 l) {inQ : (I.rec7 l Z).what₂.Tup → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop}
  {T : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ} {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)} {J : Formalism.L2.Herm.TwChJointS T H}
  {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)}

structure StdP {W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F} {Lv : SymmetricTwistedLevelData W} (P : TwPTiedS Lv) (E : TwPEvzS P) : Prop where

  what₂ : ∀ u a ha, I.ReadsP a (P.cls u a ha).lev.Lb (P.cls u a ha).lev.U (P.cls u a ha).lev.chi (fun c => ((P.cls u a ha).y c).1)
    (P.cls u a ha).lat fun c s => ((P.cls u a ha).stabI c s).1

  eW : ∀ u a ha z c (s : FrP (I.rec7 l Z)) s', s'.1 = s.1 → (P.val u a ha).eW z c s = z c s'

  z0 : ∀ u a ha h1, (P.til u a ha h1).z0 = TC.z0 X u

  eWz : ∀ u a z, E.eWz u a z = z

variable {I l Z l0} {W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F} {Lv : SymmetricTwistedLevelData W}

end Tw

def StdTw (l0 : I.Law0 l) {cf : Formalism.L2.Host.CharFrame (I.rec7 l Z)} {nch : NChoice (I.rec7 l Z)}
    {tp : Formalism.L2.Host.TupTied (I.rec7 l Z) cf nch} {C : ColsTiedSym (I.rec7 l Z)} (t : SymmetricTwistedColumnsAtPrimes tp C (I.tw l l0 Z)) : Prop :=
  I.StdW l Z l0 t.forms ∧ I.StdLv l Z l0 t.lv ∧ I.StdP l Z l0 t.pt t.ptE

def EntOk {D : D7} {Y : DivX D} {Tw : TwForms D} (E : KerEnt D Y Tw) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) : Prop :=
  (∃ kf : ∀ u μ w, LevFree Y u μ w → GL3Columns.KFTie E (O u μ) w, ∀ u μ w (h : LevFree Y u μ w), (kf u μ w h).UnIs) ∧ AdaptedTh E O

end GlobalTheory.Mem.Col2.TC

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host

namespace GlobalTheory.Mem.R3.Tr

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

def real {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} (R : RealDat a.D A Ks) :
    @RealDat b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) :=
  @RealDat.mk b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK)
    (toLevCh := levCh b R.toLevCh)
    (hv0 := (by with_unfolding_all exact (R.hv0 :)))
    (eG := (by with_unfolding_all exact (R.eG :)))
    (pl := (by with_unfolding_all exact (R.pl :)))
    (Sb := (by with_unfolding_all exact (R.Sb :)))
    (θ := (by with_unfolding_all exact (R.θ :)))
    (ψ := (by with_unfolding_all exact (R.ψ :)))
    (MY := fun j => (by with_unfolding_all exact ((ds b (R.MY j)) :)))
    (MX := (by with_unfolding_all exact ((ds b R.MX) :)))
    (MW := fun i σ => (by with_unfolding_all exact ((ds b (R.MW ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (σ :))))) :)))
    (cX := (by with_unfolding_all exact ((coefA b R.cX) :)))
    (cV := fun i => (by with_unfolding_all exact ((coefA b (R.cV ((by with_unfolding_all exact (i :))))) :)))
    (B := (by with_unfolding_all exact ((famReal b R.B) :)))
    (prX := (by with_unfolding_all exact (R.prX :)))
    (HX := (by with_unfolding_all exact (R.HX :)))
    (HV := (by with_unfolding_all exact (R.HV :)))
    (HE := (by with_unfolding_all exact (R.HE :)))
    (HW := (by with_unfolding_all exact (R.HW :)))
    (gE := (by with_unfolding_all exact (R.gE :)))
    (gW := (by with_unfolding_all exact (R.gW :)))
    (jX := (by with_unfolding_all exact (R.jX :)))
    (jV := (by with_unfolding_all exact (R.jV :)))
    (νY := (by with_unfolding_all exact (R.νY :)))
    (fdY := (by with_unfolding_all exact (R.fdY :)))
    (ν0 := (by with_unfolding_all exact (R.ν0 :)))
    (fd0 := (by with_unfolding_all exact (R.fd0 :)))
    (νX := (by with_unfolding_all exact (R.νX :)))
    (fdX := (by with_unfolding_all exact (R.fdX :)))
    (νV := (by with_unfolding_all exact (R.νV :)))
    (fdV := (by with_unfolding_all exact (R.fdV :)))
    (νW := (by with_unfolding_all exact (R.νW :)))
    (fdW := (by with_unfolding_all exact (R.fdW :)))
    (ωY := (by with_unfolding_all exact (R.ωY :)))
    (ωX := (by with_unfolding_all exact (R.ωX :)))
    (ωP := (by with_unfolding_all exact (R.ωP :)))
    (vac := (by with_unfolding_all exact (R.vac :)))
    (vacX := (by with_unfolding_all exact (R.vacX :)))
    (vacP := (by with_unfolding_all exact (R.vacP :)))
    (vY := (by with_unfolding_all exact (R.vY :)))
    (vX := (by with_unfolding_all exact (R.vX :)))
    (vP := (by with_unfolding_all exact (R.vP :)))
    (ItY := (by with_unfolding_all exact (R.ItY :)))
    (ItX := (by with_unfolding_all exact (R.ItX :)))
    (ioY := (by with_unfolding_all exact ((ioYB b R) :)))
    (ioX := (by with_unfolding_all exact ((ioXB b R) :)))
    (Th := (by with_unfolding_all exact (R.Th :)))
    (BV := (by with_unfolding_all exact (R.BV :)))
    (ioP := (by with_unfolding_all exact (R.ioP :)))
    (thF := (by with_unfolding_all exact (R.thF :)))
    (thG := (by with_unfolding_all exact (R.thG :)))
    (nW := (by with_unfolding_all exact (R.nW :)))
    (FW := (by with_unfolding_all exact (R.FW :)))
    (mu := (by with_unfolding_all exact (R.mu :)))
    (twPl := (by with_unfolding_all exact (R.twPl :)))
    (kap := (by with_unfolding_all exact (R.kap :)))
    (lam := (by with_unfolding_all exact (R.lam :)))
    (err0 := (by with_unfolding_all exact (R.err0 :)))

theorem real_ioY {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} (R : RealDat a.D A Ks) :
    @HEq (IoYT (@MultT a.D) R) ((R.ioY)) _ (@RealDat.ioY b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R)) :=
  (by with_unfolding_all exact ((castAlong (congrArg (fun m : type_of% (@MultT a.D) => IoYT (@m) R) (multT_eq b a)) ((by with_unfolding_all exact (R.ioY :)))).2 :))

theorem real_ioX {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} (R : RealDat a.D A Ks) :
    @HEq (IoXT (@MultT a.D) R) ((R.ioX)) _ (@RealDat.ioX b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R)) :=
  (by with_unfolding_all exact ((castAlong (congrArg (fun m : type_of% (@MultT a.D) => IoXT (@m) R) (multT_eq b a)) ((by with_unfolding_all exact (R.ioX :)))).2 :))

def real3 {A : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m} (R : RealDat3 a.D A Ks) :
    @RealDat3 b.D G _ _ Pl0 I0 T (famInThreeCoefficientChange b A) Ks _ _ (alg b iK) :=
  @RealDat3.mk b.D G _ _ Pl0 I0 T (famInThreeCoefficientChange b A) Ks _ _ (alg b iK) ((by with_unfolding_all exact ((real b R.toRealDat) :))) ((by with_unfolding_all exact (R.plI :))) ((by with_unfolding_all exact (R.SF :))) ((by with_unfolding_all exact (R.phs :)))
    ((by with_unfolding_all exact (R.lam3 :)))

end GlobalTheory.Mem.R3.Tr

end
end

section

noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure New (D : D7) : Type 1 where
  Z : SNew D
  N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V
  h : D.what₂.Word → ℝ

def reD (D : D7) (Z : New D) : D7 := GlobalTheory.EX.OB.setDiv (reS D Z.Z) Z.N Z.h



def SameForms0LevelsAndValues {D : D7} (Z : New D) (F : ∀ u, Forms0 D u) (F' : ∀ u, Forms0 (reD D Z) u) : Prop :=
  ∀ u : D.what₂.Word, (F' u).cls0.lev = (F u).cls0.lev ∧ (F' u).cls0.y = (F u).cls0.y ∧ (F' u).val0.eY = (F u).val0.eY

variable {D : D7} (Z : New D)

def wd (u : D.what₂.Word) : (reD D Z).what₂.Word := u

def New.self (D : D7) : New D := ⟨SNew.self D, fun u => (D.div.Nu u).L, D.div.h⟩

def New.ofDiv (D : D7) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) : New D := ⟨SNew.self D, N, h⟩



def reX (X : HidaSetting D) : HidaSetting (reD D Z) := { X with }

end GlobalTheory.Mem.SRe

end
end

section

noncomputable section

namespace GlobalTheory.Mem.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

structure Obj2 (D : D7) : Type 1 where

  gatT : GatTies D

  th : ThetaX D

  cmp : LatCmp D

  tw : TwForms D

  Gy : G.LatInst D

  errX : ErrX D

  nch : NChoice D

  xd : ThData D

  lev : LevelData D

  X : DivX D

  p0 : BaseLevelRowSide D

  ker : ∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    LocalToGlobal₂ D gatT cmp tw u w h (Gy.Ch u w h)

  amb : AmbForm D (RowSide.sharp D)

  amb0 : AmbForm D p0.s

  gauge : letI := D.host.cmStar; GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig

def layObj {D : D7} (Y : Lay D) : Obj2 D := { Y with }

def Obj2.tr {D : D7} (O : Obj2 D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) : Obj2 (setDiv D N h) where
  gatT := gatTr N h O.gatT
  th := thTr N h O.th
  cmp := cmpTr N h O.cmp
  tw := twTr N h O.tw
  Gy := latTr N h O.Gy
  errX := errTr N h O.errX
  nch := nchTr N h O.nch
  xd := xdTr N h O.xd
  lev := O.lev
  X := divTr N h O.X
  p0 := ⟨sideTr N h O.p0.s⟩
  ker := fun u w g => { O.ker u w g with }
  amb := { O.amb with }
  amb0 := { O.amb0 with }
  gauge := O.gauge

def pointPropertyOfObjects (QO : ∀ D : D7, Obj2 D → Prop) : PtProp := fun D _ gatT _ Gy _ X _ ex =>
  QO D { gatT := gatT, th := ex.th, cmp := ex.cmp, tw := ex.tw, Gy := Gy, errX := ex.errX, nch := ex.nch, xd := ex.xd,
         lev := ex.lev, X := X, p0 := ex.p0, ker := ex.ker, amb := ex.amb, amb0 := ex.amb0, gauge := ex.gauge }

def allDiv (QO : ∀ D : D7, Obj2 D → Prop) (D : D7) (Y : Lay D) : Prop := ∀ N h, QO (setDiv D N h) ((layObj Y).tr N h)

def extraObj {D : D7} {L : SizeData₂ D} {gatT : GatTies D} {Gx : G.Inst D L} {Gy : G.LatInst D} {K : G.Consts} {X : DivX D}
    {cX : ExtraC} (ex : Extra D L gatT Gx Gy K X cX) : Obj2 D :=
  { gatT := gatT, th := ex.th, cmp := ex.cmp, tw := ex.tw, Gy := Gy, errX := ex.errX, nch := ex.nch, xd := ex.xd,
    lev := ex.lev, X := X, p0 := ex.p0, ker := ex.ker, amb := ex.amb, amb0 := ex.amb0, gauge := ex.gauge }

def ofObj {D : D7} (O : Obj D) : Obj2 D := extraObj O.ex

def pointObj {C : FC} (p : Pt C) : Obj2 p.D := extraObj p.xa.ex

theorem ofObj_obj {C : FC} {D : D7} (Y : Lay D) (p : LedPart C Y) : ofObj (Y.obj p) = layObj Y := rfl

theorem pointObj_pt {C : FC} {D : D7} {Y : Lay D} (p : LedPart C Y) : pointObj p.pt = (layObj Y).tr (nPrime p.L) p.ht := rfl

end GlobalTheory.Mem.Top

end
end
