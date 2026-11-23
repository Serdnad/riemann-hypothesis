module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle032
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle033
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeIsobaric
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle013
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle003
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroTypeInertia
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.MoyPrasadJacquetIsoTrivial
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelPurity
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle003
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle006
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Lean.Meta.Injective

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def PositionMv (𝒮 : Slots) : Prop :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj2 (w.D Z)) (x : Wit 𝒮 K w Z O)
    (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (O' : Obj2 (w.D (Db.setDivZ Z N h))), O' = O.tr N h →
    ∀ (col : ColumnDataSplitPrimes K w (Db.setDivZ Z N h)) (n : NchT w (Db.setDivZ Z N h) x.Wt O'.nch),
    ∃ t : RowsT K w (Db.setDivZ Z N h) x.Wt O'.p0, ObjT O' t ∧
      Nonempty (𝒮.Rx K B f T w (Db.setDivZ Z N h) x.Wt O'.p0 t) ∧
      Nonempty (𝒮.Nx K B f T w (Db.setDivZ Z N h) x.Wt O'.p0 t O'.nch n O'.xd) ∧
      Nonempty (𝒮.Sx K B f T w (Db.setDivZ Z N h) x.Wt O'.p0 t col.toColT) ∧
      Nonempty (𝒮.Ox K B f T w (Db.setDivZ Z N h) x.Wt O' t)

def WitMv (𝒮 : Slots) : Prop :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj2 (w.D Z)) (x : Wit 𝒮 K w Z O)
    (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ), EntC x.ker →
    ∃ x' : Wit 𝒮 K w (Db.setDivZ Z N h) (O.tr N h), EntC x'.ker

end GlobalTheory.Mem.Top.Bl

end
end

section

noncomputable section

namespace GlobalTheory.Mem.SRe

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.DIV
  Formalism.MainNotions Formalism.L2.Forms NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl

attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure RowPk (D : D7) : Type 1 where
  G' : Type
  [grp : Group G']
  [fin : Fintype G']
  Pl0 : Type
  T : Type
  A : FamIn D.what₂.LL G' Pl0 T D.R.m
  Ks : Type
  [fld : Field Ks]
  [nf : NumberField Ks]
  [iK : Algebra Ks D.what₂.LL]
  R : RealDat D A Ks
  F : Face D A
  eE : D.what₂.EE →ₗ[ℂ] R.HE.H

attribute [instance] RowPk.grp RowPk.fin RowPk.fld RowPk.nf RowPk.iK

def RowPk.SAt {D : D7} (p : RowPk D) (F₀ : ∀ u, Forms0 D u) : Type 1 := Top.Bl.SAt p.R p.F p.eE F₀

def upL {B : Base} {C : Cols B} (a : Late B C) (S' : SStage B C a.W) (N : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V)
    (h : B.Word → ℝ) : Late B C := ⟨a.W, (Db.setDivZ a N h).V, S', a.N, a.G⟩



def RowPk.up {B : Base} {C : Cols B} (a : Late B C) (S' : SStage B C a.W) (N : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V)
    (h : B.Word → ℝ) (p : RowPk a.D) : RowPk (upL a S' N h).D :=
  @RowPk.mk (upL a S' N h).D p.G' p.grp p.fin p.Pl0 p.T (famM (upL a S' N h) p.A) p.Ks p.fld p.nf (alg (upL a S' N h) p.iK)
    (real (upL a S' N h) p.R) (face (upL a S' N h) p.F) ((p.eE))

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}



def pkOf {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (r : RowsT K w Z Wt p0) : RowPk (Late.D Z) where
  G' := _
  Pl0 := _
  T := _
  Ks := _
  A := _
  R := r.r.z.R.toRealDat
  F := r.r.z.F.lv2
  eE := r.r.Y.eE



theorem sx_eq {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (r : RowsT K w Z Wt p0) (col : ColT w Z) :
    SX K B f T w Z Wt p0 r col = (pkOf r).SAt fun u => (col.C.forms u).to0 := (Eq.refl (SX K B f T w Z Wt p0 r col))



def LevelThreeCondition (𝒮 : Slots) : Prop :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (l : Lv3 𝒮 K w Z) (S' : SStage B w.C Z.W)
    (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ),
    ∃ l' : Lv3 𝒮 K w (upL Z S' N h), pkOf l'.what₂ = (pkOf l.what₂).up Z S' N h



def SxMv : Prop :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z))
    (r : RowsT K w Z Wt p0) (col : ColT w Z) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)
    (p0' : BaseLevelRowSide (w.D (Db.setDivZ Z N h))) (t : RowsT K w (Db.setDivZ Z N h) Wt p0') (col' : ColT w (Db.setDivZ Z N h)),
    HEq (pkOf t) ((pkOf r).up Z Z.S N h) → Nonempty (SX K B f T w Z Wt p0 r col) →
      Nonempty (SX K B f T w (Db.setDivZ Z N h) Wt p0' t col')



def SameCar {D : D7} (F F' : ∀ u, Forms0 D u) : Prop :=
  ∀ u : D.what₂.Word, (F' u).cls0.lev.Lb = (F u).cls0.lev.Lb ∧ (F' u).cls0.lev.U = (F u).cls0.lev.U ∧
    HEq (F' u).cls0.lev.chi (F u).cls0.lev.chi ∧ (F' u).cls0.y = (F u).cls0.y ∧ (F' u).val0.eY = (F u).val0.eY



def SameStd : Prop :=
  ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Zn : New (Late.D Z)) (col : ColT w Z)
    (col' : ColT w (reL Z Zn)) (F₁ : ∀ u, Forms0 (reL Z Zn).D u), SameL Z Zn (fun u => (col.C.forms u).to0) F₁ →
      SameCar F₁ fun u => (col'.C.forms u).to0

end GlobalTheory.Mem.SRe

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}
  {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀} {o : q.Over}

structure Moved.Copy (m : Moved o) : Prop where
  core : HEq m.z.core (coreJ (a := ⟨Z₀.W, Z₀.V, Z₀.S, Z₀.N, Z₀.G⟩) ⟨q.W o.η o.hη, o.V, o.S, o.N, o.G⟩ z₀.core)
  R : HEq m.z.R (real3 (a := ⟨Z₀.W, Z₀.V, Z₀.S, Z₀.N, Z₀.G⟩) ⟨q.W o.η o.hη, o.V, o.S, o.N, o.G⟩ (iK := z₀.alg) z₀.R)

structure Moved.Coh (m : Moved o) : Prop where
  tupT : HEq m.y.tupT q.y.tupT
  PY : HEq m.y.PY.ψ q.y.PY.ψ
  PW : HEq (fun i => (m.y.PW i).ψ) fun i => (q.y.PW i).ψ
  rep : HEq m.t.rep q.t.rep
  jE : ∀ b, HEq (m.t.ch b).jE (q.t.ch b).jE
  jM : ∀ b, HEq (m.t.ch b).jM (q.t.ch b).jM
  jX : ∀ b, HEq (m.t.ch b).jX (q.t.ch b).jX
  eW : HEq m.t.lf.eW q.t.lf.eW
  jMt : HEq m.t.lf.jMt q.t.lf.jMt

structure ReadPk.Pin {m : Moved o} {s : Side0 o} (r : ReadPk m s) : Prop where
  rep : ∀ π, (principalLevelFrame.rowRepR m.z.R.θ (r.Y.eFT π)).Iso (m.t.rep π)
  jE : ∀ x, HEq (r.Y.Ish.jE x).1 ((m.t.ch true).jE x)
  heq_eigen_embedding_zero : ∀ x, HEq (r.Y.Iz.jE x).1 ((m.t.ch false).jE x)
  eW : ∀ i x, HEq (r.Y.mj.eW i x) (m.t.lf.eW i x)
  jMt : ∀ μ h i x, HEq (r.Y.IL.jMt μ h i x).1 (m.t.lf.jMt μ i x)


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure Pre2 (K : Ctx) (w : ColW B f T) : Type 1 where
  Z₀ : w.Lt
  hX : B.fields.Ok
  Wt : Set B.places.Pl
  z : Dat (w.st Z₀) w.I hX T Wt
  q : RowPk w z
  g : GIs2 K w Z₀.G
  coh : Coh B T
  grp : GrpTrue Z₀.N f
  grpAt : GrpAt (w.st Z₀) w.I
  kap : DV.KapDef (w.D Z₀)
  intersectionNumber_baseChange : Holds z.R z.F
  exAt : z.R.toRealDat.ExAt
  inGeo : GlobalTheory.RealGeo.InGeo z.geo
  core : CoreP z
  exact : Wt = z.W1 (F0K K.s (w.D Z₀))
  sub : ∀ v ∈ Wt, B.places.resChar v ∈ T.pl
  supp : ∀ v, v ∉ Wt → T.psi v = 1
  std : z.Std

def HasPk : WP := fun K _ _ _ w => Nonempty (Pre2 K w)

structure HoldsL {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) : Prop where
  heckeR : ∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint
  heckeL : ∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint
  hecke : R.PHecke F
  gUnit : R.PGUnit F
  gEquiv : R.PGEquiv F
  block : (R.toCx3 F).zs.InBlock
  liftTest : Formalism.IndefR.Rat.LiftTest (R.toCx3 F)
  liftTestB : Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false
  liftOnto : ∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW
  unif : R.toRealDat.LUnif
  mLat : (R.toCx3 F).MLat false
  levW : R.PLevW F
  thmA : R.PThmA
  sumW : (R.toCx3 F).PartsW false
  aux : UnusedChoiceStatements R F
  ok : A3.fam3.Ok3 1
  sep : A3.fam3.TypesSep3

theorem HoldsL.of_holds {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} (h : Holds R F) :
    HoldsL R F :=
  ⟨h.prim.heckeR, h.prim.heckeL, h.prim.hecke, h.prim.gUnit, h.prim.gEquiv, h.prim.block, h.prim.liftTest, h.prim.liftTestB,
    h.prim.liftOnto, h.prim.unif, h.prim.mLat, h.prim.levW, h.prim.thmA, h.prim.sumW, h.aux, h.ok, h.sep⟩

def LowerUnitaryCaseCondition : Prop := GroupRetwisting.Step KPx (fun _ _ _ _ => True) fun K B f T => ∀ w : ColW B f T, Pinned K B f T w →
  ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I →
    z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo → HoldsL z.R z.F

def WeightCaseCondition : Prop := StepW Start fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
  (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → DV.KapDef (w.D Z) → z.R.toRealDat.ExAt →
    GlobalTheory.RealGeo.InGeo z.geo → CoreP z → GIs2 K w Z.G → Wt = z.W1 (F0K K.s (w.D Z)) → (∀ v ∈ Wt, B.places.resChar v ∈ T.pl) →
    Holds z.R z.F

def BkLaw (D : D7) : Prop := WeightDegreeSizes.RationalMapValues D → D.BuRational

structure St {K : Ctx} (P : Pre2 K w) : Type 1 where
  o : P.q.Over
  fits : o.Fits
  G_eq : o.G = P.Z₀.G
  etaF : o.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF)
  bk : BkLaw (w.D o.Z)
  m : Moved o
  copy : m.Copy
  coh : m.Coh
  s : Side0 o
  r : ReadPk m s
  pin : r.Pin

def HasBare : WP := fun K _ _ _ w => ∃ (P : Pre2 K w) (x : St P), IsEmpty x.o.N.nd.Loc ∧ ∀ j v, x.o.η j v = 0

structure RowsSame {K : Ctx} {Z Z' : w.Lt} {p0 : BaseLevelRowSide (w.D Z)} {p0' : BaseLevelRowSide (w.D Z')} (t : RowsT K w Z Wt p0)
    (t' : RowsT K w Z' Wt p0') : Prop where
  Xg : t'.r.z.Xg = t.r.z.Xg
  tr : t'.r.z.tr = t.r.z.tr
  core : HEq t'.r.z.core (coreJ (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ t.r.z.core)
  R : HEq t'.r.z.R (real3 (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ (iK := t.r.z.alg) t.r.z.R)
  cG : HEq t'.r.z.cG t.r.z.cG
  tup : HEq t'.r.Y.tup t.r.Y.tup
  tupT : HEq t'.r.Y.tupT t.r.Y.tupT
  PY : HEq t'.r.Y.PY.ψ t.r.Y.PY.ψ
  PW : HEq (fun i => (t'.r.Y.PW i).ψ) fun i => (t.r.Y.PW i).ψ
  rep : HEq (fun π => principalLevelFrame.rowRepR t'.r.z.R.θ (t'.r.Y.eFT π)) fun π => principalLevelFrame.rowRepR t.r.z.R.θ (t.r.Y.eFT π)
  jE : HEq (fun x => (t'.r.Y.Ish.jE x).1) fun x => (t.r.Y.Ish.jE x).1
  heq_eigen_embedding_zero : HEq (fun x => (t'.r.Y.Iz.jE x).1) fun x => (t.r.Y.Iz.jE x).1
  eE : HEq t'.r.Y.eE t.r.Y.eE
  jA : HEq t'.r.Y.jA t.r.Y.jA
  jA0 : HEq t'.r.Y.jA0 t.r.Y.jA0
  eMt : HEq t'.r.Y.eMt t.r.Y.eMt
  eW : HEq t'.r.Y.mj.eW t.r.Y.mj.eW
  jW : HEq t'.r.Z.jW t.r.Z.jW
  eRR : HEq t'.r.Z.eRR t.r.Z.eRR
  eRR0 : HEq t'.r.Z.eRR0 t.r.Z.eRR0

end GlobalTheory.Mem.R3.Rw

end
end

section

namespace GlobalTheory.Mem.LiteralAutomorphy

open ReciprocityTheory.Gal Formalism.GaloisCohomology GlobalTheory.Published

structure LitLoc : Prop where
  bz : BernsteinZelevinskyFiniteness
  bern : BernsteinUnitaryProductIrreducible
  geo : GeometricLemma
  zel : ZelevinskyPolynomialRing
  disj : TotallyDisjointProductIrreducible
  mp : MoyPrasadJacquetIso
  theta : MinguezThetaGL
  temp : TemperedProductOfSquareIntegrable
  seg : EssSquareIntegrableSegments
  sq : SquareIntegrableSegment
  unit : UnitaryDualGL
  gen : GenericUnlinkedGL
  multi : LanglandsMultisegments
  exh : LanglandsExhaustionGL
  cos : StandardCosocleGL
  llc : LocalLanglandsExists
  conv : LocalConverseGL
  dzc : DepthZeroCuspidalLL
  dzi : DepthZeroInduction
  dzt : DepthZeroTypeInertia
  brauer : BrauerDegreeZero
  chev : ChevalleyUnits
  green : GreenRegularCharacters

structure LitAut : Prop where
  decay : CuspRapidDecay
  hc : HarishChandraFinite
  fin : AutomorphicFormsFiniteGL
  js : JacquetShalika
  cusp : CuspidalSpectrumGL
  mw : DiscreteSpectrumResidual
  bc : BaseChangeIsobaric
  gk : GelfandKazhdanDual
  gal : GaloisRepOfPolarizedPair
  car : CaraianiLocalGlobalDual
  ctemp : CaraianiTempered
  pur : ClozelPurity
  coh : ClozelCohomological
  art : GlobalArtinReciprocity
  ray : RayClassFieldSt
  chA : HeckeLAdicCharacterAbove
  chW : AlgebraicCharacterWD
  berger : DeRhamPotSemistable

structure LitCoh : Prop where
  pt : PoitouTateNormalised
  lf : LocalFiniteness
  lt : LocalTateDuality
  le : LocalEulerChar
  gf : GlobalFiniteness
  ge : GlobalEulerChar
  uo : UnramifiedOrthogonality
  gw : GreenbergWiles
  lfK : LocalFinitenessK
  ltK : LocalTateDualityK
  leK : LocalEulerCharK
  bk : BlochKatoLocal

structure LitCM : Prop where
  hb : HilbertBlumenthal
  gm : GrothendieckDeformation
  dr : AbelianDeRham
  dual : AbelianDualCrystal
  per : PeriodComparison
  gmp : GaussManinPeriods
  st : SerreTateGoodReductionSt
  cm : EllipticMainTheoremCM
  hj : HilbertClassFieldJ
  dri : SiegelKlingenDeligneRibet
  pz : PartialZetaFunctionalEquation
  fe : HeckeTateFunctionalEquation

structure LitN : Prop where
  loc : LitLoc
  aut : LitAut
  coh : LitCoh
  cm : LitCM

end GlobalTheory.Mem.LiteralAutomorphy
end
