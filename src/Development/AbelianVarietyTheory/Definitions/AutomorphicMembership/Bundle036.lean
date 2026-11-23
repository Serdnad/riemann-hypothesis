module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle034
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistDataAgreeAcrossCoefficients
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle061
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024

@[expose] public section

section

noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option genInjectivity false
set_option genSizeOfSpec false


variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

abbrev Dof (x : St P) : D7 := (w.st x.o.Z).toD7

abbrev cfOf (x : St P) : CharFrame (Dof x) := TC.cf w.I w.l x.o.Z


open Classical in
def QOf (P : Pre2 K w) (v : B.places.Pl) : Finset (HeightOneSpectrum (𝓞 B.host.E)) := if v ∈ P.Wt then T.Q v else ∅

structure LA (hL : GlobalTheory.Published.LocalLanglandsGL) (x : St P) : Type 1 where
  a : StA hL (Dof x) (cfOf x) (repOf x.r.Y)
  Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (Dof x).host.E)) → PlE (Dof x).host
  Pq_over : ∀ v, NG.OverPl (Pq v) v
  sel : Set.range Pq = Set.range w.I.sel

structure LI (hL : GlobalTheory.Published.LocalLanglandsGL) (x : St P) : Type 1 extends LA hL x where
  mt : InMt x.r.Y (cfOf x) w.I.xi (QOf P)
  rat : InRat x.r.Y x.m.z.cG
  cusp : RowCusp (Dof x) a.A.row

structure SeriesLevel (hL : GlobalTheory.Published.LocalLanglandsGL) (x : St P) : Type 1 extends LI hL x where
  b : SeriesState x.m.z.geo a rat mt.ad.PV Pq

structure StrictHenselianAcyclic (hL : GlobalTheory.Published.LocalLanglandsGL) (x : St P) : Type 1 extends LI hL x where
  b : ModuliPointsState x.m.z.geo a rat mt.ad.PV Pq

structure LC (hL : GlobalTheory.Published.LocalLanglandsGL) (x : St P) : Type 1 extends StrictHenselianAcyclic hL x where
  c : StC mt b T.k T.psi

abbrev AllSt (p : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), St P → Prop) : Prop :=
  StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), p K B f T w P x

variable (hL)

def SMt : Prop := AllSt fun _ _ _ _ w P x => Nonempty (InMt x.r.Y (cfOf x) w.I.xi (QOf P))

structure Kept {D D' : D7} (c : NChoice D) (c' : NChoice D') : Prop where
  gal : GlobalTheory.TwistChoice.SameGalois D.nd D'.nd
  set : GlobalTheory.TwistChoice.TwistDataAgreeAcrossCoefficients D.ntw D'.ntw
  forms : GlobalTheory.TwistChoice.SameForms D.nexp D'.nexp
  br : HEq D.ntwbr D'.ntwbr
  twI : HEq c.twI c'.twI
  sd : HEq c.sd c'.sd
  Q : HEq c.Q c'.Q
  k : HEq c.k' c'.k'
  psi : HEq c.psi' c'.psi'

end GlobalTheory.HeightCounting.Up

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.RowEx
open Formalism.L2.Host (HChar)
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.LiteralAutomorphy

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev GKey (P : Pre) : Type :=
  HeightOneSpectrum (𝓞 P.host.F) × HeightOneSpectrum (𝓞 P.host.E) × (Fin P.R.m → HChar P.host.E)

def gkeyOf {X : Stages} {T : Type} {L : Formalism.IndefR.Links.LevCh X.toD7 T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) : GKey X.B.toPre :=
  (G.pl.v0, G.pl.w G.pl.v0, fun a => G.ch.chiH (a.1 + 1))

def GKeyFin : Prop := ∀ (P : Pre) (c : ℝ), ∃ 𝒦 : Set (GKey P), 𝒦.Finite ∧
  ∀ (X : Stages) (T : Type) (L : Formalism.IndefR.Links.LevCh X.toD7 T) (sc : GlobalTheory.ChiGrid.Consts) (G : GridData L sc), X.B.toPre = P → sc.cGap = c →
    ∃ κ ∈ 𝒦, HEq (gkeyOf G) κ

def WeilEx : Prop := BigR fun R sc => ∀ G : GridData R.toLevCh sc, ∃ W : G.Weil, W.Over R ∧ Nonempty (GridChoice W Set.univ)

def NFSq : Prop := ∃ CF0 : ℝ, ∀ ε CF : ℝ, CF0 ≤ CF → ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
  GlobalTheory.SqTop.Rec large₂ → ∀ (T : Type) (L : Formalism.IndefR.Links.LevCh D T) (μ₀ : T), L.Is μ₀ → ∀ G : GridData L ⟨1, CF, large₂.sc.b⟩,
    InNF fun _ σ => GlobalTheory.BigTop.Fun.SqIn G μ₀ σ

def TrSq : Prop := OnAgree fun {_ _ _ _ _ _ _} G G' _ _ _ _ μ₀ μ₀' _ => ∀ (M : IntermediateField ℚ ℂ) (σ : M →+* ℂ),
  GlobalTheory.BigTop.Fun.SqIn G μ₀ σ → GlobalTheory.BigTop.Fun.SqIn G' μ₀' σ

def Full {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) {sc : GlobalTheory.ChiGrid.Consts}
    (G : GridData R.toLevCh sc) : Prop :=
  ∃ W M ρ ξ cv rm S rp n e c, (⟨sc, G, W, M, ρ, ξ, cv, rm, S, rp, n, e, c⟩ : Choice R).Is ∧
    (⟨sc, G, W, M, ρ, ξ, cv, rm, S, rp, n, e, c⟩ : Choice R).FieldOK ∧ GlobalTheory.BigTop.Fun.SqIn G A.μ0 D.what₂.embLL

def GridAt (s : Scale) (CF : ℝ) (X : Stages) (f : Fr X.B.toPre) (Ξ : Set (HChar X.B.host.E)) : Prop :=
  ∀ large₂ : SizeData₂ X.toD7, large₂.sc = s → GlobalTheory.SqTop.Rec large₂ → ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type)
    (A : FamIn X.toD7.what₂.LL Γ Pl0 T X.toD7.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks X.toD7.what₂.LL]
    (R : RealDat X.toD7 A Ks) (F : Face X.toD7 A), HidaSetting large₂ R F → R.C = Fr.at X f → TwistPlacesOffPrimeQZero R.toLevCh →
    (∀ t, ∃ ξ ∈ Ξ, HEq (R.toLevCh.xiH t) ξ) → ∀ G₀ : GridData R.toLevCh ⟨1, CF, s.b⟩,
      ∃ G : GridData R.toLevCh ⟨1, CF, s.b⟩, gkeyOf G = gkeyOf G₀ ∧ Full R G

def ExGrid : Prop := ∃ CF0 : ℝ, ∀ ε CF : ℝ, CF0 ≤ CF → ∃ x₀ : ℝ, ∀ s : Scale, s.eps = ε → x₀ ≤ s.x →
  ∀ (P : Pre) (f : Fr P) (Ξ : Set (HChar P.host.E)), Ξ.Finite → ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧
    ∀ (X : Stages) (f' : Fr X.B.toPre) (Ξ' : Set (HChar X.B.host.E)), X.B.toPre = P → HEq f' f → HEq Ξ' Ξ →
      (∀ z ∈ S, z ∈ Set.range X.toD7.what₂.embLL) → GridAt s CF X f' Ξ'

def GridA (CF : ℝ) : AtP := fun K B f T => ∀ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W)
  (N : NStage B C W) (G : GJStage B C), GridAt K.s CF ⟨B, C, W, V, S, N, G⟩ f (T.set f)

end GlobalTheory.Mem.LiteralAutomorphy

end
end
