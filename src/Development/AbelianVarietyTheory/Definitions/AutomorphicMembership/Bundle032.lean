module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle030
public import Formalism.LocalToGlobal.HilbertRowConditions.Bundle001
public import Formalism.LocalToGlobal.KernelLattices.TopPin
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

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Mem.SRe

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.MainNotions Formalism.L2.Forms NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Top.Bl

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section PiLocalization₂

variable {B : Base} {C : Cols B} (a : Late B C) (Z : New a.D)



def setV : DivStage B C a.W where
  div := ((reD a.D Z).div)
  div_good := (a.V.div_good)
  jEE := (a.V.jEE)
  jEE_basis := (a.V.jEE_basis)
  jN := (a.V.jN)
  jN_basis := (a.V.jN_basis)
  Dall_eq := (a.V.Dall_eq)
  delP_eq := (a.V.delP_eq)
  nuIn := (a.V.nuIn)
  nuIn_inj := (a.V.nuIn_inj)
  nuIn_range := (a.V.nuIn_range)
  nuIn_jN := (a.V.nuIn_jN)
  nuIn_norm := (a.V.nuIn_norm)
  jEE_norm := (a.V.jEE_norm)

def reL : Late B C := ⟨a.W, setV a Z, (reStage a.st Z.Z), a.N, a.G⟩



def XL (X : HidaSetting a.D) : HidaSetting (reL a Z).D := (reX Z X)



theorem hL {X : HidaSetting a.D} (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf a.D) :
    (XL a Z X).B.I = Formalism.L2.SG.InstExistsPf.instOf (reL a Z).D := (h)



def gdL {X : HidaSetting a.D} (G : GoodOp X) : GoodOp (XL a Z X) := ⟨(G.Rg), (G.Rg_spec)⟩



def tL (t : GA a.D (a.D.sp.Y 0)) : GA (reL a Z).D ((reL a Z).D.sp.Y 0) := (t)



def jL {X : HidaSetting a.D} {G : GoodOp X} (j : a.D.what₂.EE ≃ₗᵢ[ℂ] EEC X G) :
    (reL a Z).D.what₂.EE ≃ₗᵢ[ℂ] EEC (XL a Z X) (gdL a Z G) := (j)



def SameL (F₀ : ∀ u, Forms0 a.D u) (F₁ : ∀ u, Forms0 (reL a Z).D u) : Prop := SameForms0LevelsAndValues Z F₀ ((F₁))

variable {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]



def eL (R : RealDat a.D A Ks) (eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H) :
    letI := alg (reL a Z) iK; (reL a Z).D.what₂.EE →ₗ[ℂ] (real (reL a Z) R).HE.H := (eE)



def SAtL (R : RealDat a.D A Ks) (F : Face a.D A) (eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H) (F₁ : ∀ u, Forms0 (reL a Z).D u) : Type 1 :=
  letI := alg (reL a Z) iK; SAt (real (reL a Z) R) (face (reL a Z) F) (eL a Z R eE) F₁



def SAtL.pt {R : RealDat a.D A Ks} {F : Face a.D A} {eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H} {F₁ : ∀ u, Forms0 (reL a Z).D u}
    (s : SAtL a Z R F eE F₁) : GA (reL a Z).D ((reL a Z).D.sp.Y 0) := letI := alg (reL a Z) iK; SAt.t s

end PiLocalization₂



def MvSee : Prop := ∀ {B : Base} {C : Cols B} (a : Late B C) (Z : New a.D) {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type}
    {A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
    (R : RealDat a.D A Ks) (F : Face a.D A) (X : HidaSetting a.D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf a.D)
    (t : GA a.D (a.D.sp.Y 0)), SeeAt R F X h t →
    letI := alg (reL a Z) iK; SeeAt (real (reL a Z) R) (face (reL a Z) F) (XL a Z X) (hL a Z h) (tL a Z t)



def MvEv : Prop := ∀ {B : Base} {C : Cols B} (a : Late B C) (Z : New a.D) {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type}
    {A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
    (R : RealDat a.D A Ks) (F : Face a.D A) (X : HidaSetting a.D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf a.D)
    (G : GoodOp X) (t : GA a.D (a.D.sp.Y 0)) (c : ℝ), EvalTieT (MP R) R.ν0 R.fd0 (EP R F) X G (iotaX X h).toMulEquiv t c →
    letI := alg (reL a Z) iK
    EvalTieT (MP (real (reL a Z) R)) (real (reL a Z) R).ν0 (real (reL a Z) R).fd0 (EP (real (reL a Z) R) (face (reL a Z) F)) (XL a Z X)
      (gdL a Z G) (iotaX (XL a Z X) (hL a Z h)).toMulEquiv (tL a Z t) c



def MvRowJ : Prop := ∀ {B : Base} {C : Cols B} (a : Late B C) (Z : New a.D) {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type}
    {A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
    (R : RealDat a.D A Ks) (X : HidaSetting a.D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf a.D)
    (G : GoodOp X) (t : GA a.D (a.D.sp.Y 0)) (eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H) (j : a.D.what₂.EE ≃ₗᵢ[ℂ] EEC X G), RowJ R eE X h G t j →
    letI := alg (reL a Z) iK; RowJ (real (reL a Z) R) (eL a Z R eE) (XL a Z X) (hL a Z h) (gdL a Z G) (tL a Z t) (jL a Z j)

end GlobalTheory.Mem.SRe

end
end

section

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.TieModel

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.Col2 NumberField IsDedekindDomain Formalism.L2.DIV _root_.Formalism.L2.Col

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Forms

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (hX : X.Ok)
  (P : LevFam X.E X.K R.r Pr.vGs)

def frm (y : Fin ((MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).lvlDim (g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX)) P.grp P.chr) → X.K) :
    (MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).Forms :=
  (MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).basis.equivFun.symm
    (((MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).lvlE (g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX)) P.grp P.chr).mulVec y)

theorem isFormOf_unique {V : Type} {y : V} {x x' : MtildeV W Ch sel mu P} (h : IsFormOf W Ch sel mu hX P x y)
    (h' : IsFormOf W Ch sel mu hX P x' y) : x = x' := by
  obtain ⟨F, hF, e, rfl⟩ := h
  obtain ⟨F', hF', e', rfl⟩ := h'
  have := ((mtildeKGSD W Ch sel mu).res (mtildeKOk W Ch sel mu hX)).injective (eq_of_heq (e.trans e'.symm))
  subst this
  rfl

end Forms

section Cols

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok)

end Cols

section Core

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}

end Core

section Standard

open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links



end Standard

end GlobalTheory.Mem.Top.Bl.TieModel

end
end

section

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

def coreS {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) (J : Formalism.L2.Pj.Core D) :
    Formalism.L2.Pj.Core (setDiv D N h) where
  Q := ⟨J.Q.H, J.Q.l, J.Q.c, J.Q.Dw, J.Q.Xo, J.Q.eO⟩
  U := J.U
  V := J.V
  dict := J.dict
  mu := J.mu
  Kf := J.Kf
  pb := J.pb

inductive GeoCl (Γ : GeoP) : ∀ D : D7, Formalism.L2.Pj.Core D → DivX D → Prop
  | base {D : D7} {J : Formalism.L2.Pj.Core D} {X : DivX D} : Γ D J X → GeoCl Γ D J X
  | step {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)
      {J : Formalism.L2.Pj.Core D} {X : DivX D} : GeoCl Γ D J X → GeoCl Γ (setDiv D N h) (coreS N h J) (divTr N h X)

def geoCl (Γ : GeoP) : GeoP := GeoCl Γ

theorem geoCl_of {Γ : GeoP} {D : D7} {J : Formalism.L2.Pj.Core D} {X : DivX D} (h : Γ D J X) : geoCl Γ D J X := GeoCl.base h

end GlobalTheory.Mem.Top.Bl

end
end

section

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev SExt : Type 2 := ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
  (p0 : BaseLevelRowSide (w.D Z)) (r : RowsT K w Z Wt p0) (col : ColT w Z), SX K B f T w Z Wt p0 r col → Type 1

def SExt.none : SExt := fun _ _ _ _ _ _ _ _ _ _ _ => PUnit

def SXE (E : SExt) : SPosition := fun K B f T w Z Wt p0 r col => Σ a : SX K B f T w Z Wt p0 r col, E K B f T w Z Wt p0 r col a

structure Prm (hL : GlobalTheory.Published.LocalLanglandsGL) : Type 2 where
  R : RPosition
  N : NExt hL
  S : SExt
  Γ : GeoP

variable {hL : GlobalTheory.Published.LocalLanglandsGL}

structure KPin {𝒮 : Slots} {K : Ctx} (q : WPt 𝒮 K) (t : Formalism.L2.Ker.KerEntTied q.O.ex) : Prop where
  std : TC.StdKer q.w.I q.w.l q.Z t
  O : t.O = q.x.ker.O
  ent : HEq t.ent q.x.ker.E
  adapted : t.Adapted
  top : t.TopPinned

def ZeU (𝒮 : Slots) : Prop := ∀ (K : Ctx) (q : WPt 𝒮 K), Formalism.L2.Rows.ZetaCompatible (q.w.D q.Z)

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}

def EntC {w : ColW B f T} {Z : w.Lt} {t : ColT w Z} {Y : DivX (w.D Z)} {Gy : G.LatInst (w.D Z)}
    {ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy} (k : KerT t Y Gy ker) : Prop :=
  ∃ (Pl : Examples₂.EntPl (w.D Z)) (Bs : Formalism.L2.Ker.PlaceMatrixFamily (w.D Z)) (h : Formalism.L2.Ker.KerEntHyp Pl k.O Bs Y (w.tw Z)),
    k.E = Formalism.L2.Ker.kerEntC Pl k.O Bs h

def BuiltE (𝒮 : Slots) : CP := fun K _ _ _ w Z c => ∃ b : Built 𝒮 K w Z c, EntC b.ker

def GoodE (𝒮 : Slots) : CP := fun K B f T w Z c => BuiltE 𝒮 K B f T w Z c ∧ GoodO (w.D Z) c.O.nch c.O.xd

def IsBuiltE (𝒮 : Slots) : V4.Slot := positionOf (BuiltE 𝒮)

def IsGoodE (𝒮 : Slots) : V4.Slot := positionOf (GoodE 𝒮)

theorem IsBuiltE.isBuilt {𝒮 : Slots} (K X f T c) (h : IsBuiltE 𝒮 K X f T c) : IsBuilt 𝒮 K X f T c :=
  positionOf_mono (fun _ _ _ _ _ _ _ ⟨b, _⟩ => ⟨b⟩) K X f T c h

theorem IsGoodE.isBuiltE {𝒮 : Slots} (K X f T c) (h : IsGoodE 𝒮 K X f T c) : IsBuiltE 𝒮 K X f T c :=
  positionOf_mono (fun _ _ _ _ _ _ _ h => h.1) K X f T c h

def MemberE (𝒮 : Slots) : Prop :=
  BaseCond KPx ∧ FirstG KPx (IsBuiltE 𝒮) ∧ ExportF KPx (IsBuiltE 𝒮) ∧ SecondG KPx (IsBuiltE 𝒮) (IsGoodE 𝒮)

def WitExE (𝒮 : Slots) : Prop :=
  ∀ (K : Ctx) (β : GlobalTheory.Fc.BPt K), β.Is (IsGoodE 𝒮) → ∃ q : WPt 𝒮 K, q.Is β.D β.O ∧ EntC q.x.ker

end GlobalTheory.Mem.Top.Bl

end
end
