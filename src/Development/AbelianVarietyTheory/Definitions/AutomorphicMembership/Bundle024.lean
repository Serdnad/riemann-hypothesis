module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle004
public import Formalism.LocalToGlobal.HermitianForms.Bundle011
public import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Formalism.LocalToGlobal.Columns.Adelic
public import Formalism.LocalToGlobal.Columns.RowFormsAdelic
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
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)



def SPack.re {F : ∀ u, Forms0 D u} (P : SPack D F) {F' : ∀ u, Forms0 (reD D Z) u} (h : SameForms0LevelsAndValues Z F F')
    (hF : FinX (reY Z P.Y)) : SPack (reD D Z) F' where
  X := reX Z P.X
  hb := (by with_unfolding_all exact (P.hb :))
  Y := reY Z P.Y
  fin := hF
  ψ := (by with_unfolding_all exact (P.ψ :))
  measTie := (by with_unfolding_all exact (measTie_reX Z P.measTie :))
  ψ_char := (by with_unfolding_all exact (P.ψ_char :))
  ψ_std := (by with_unfolding_all exact (P.ψ_std :))
  measCompat := (by with_unfolding_all exact (measCompat_reX Z P.measCompat :))
  locCompat := (by with_unfolding_all exact (fun w : D.what₂.Word => locCompat_reX Z (P.locCompat w) :))
  tr := (by with_unfolding_all exact (fun u : D.what₂.Word => reTr Z (P.tr u) (h u).2.1 (h u).2.2 :))
  into := (by with_unfolding_all exact (fun u : D.what₂.Word => colDictInto_reTr Z (P.tr u) (h u).2.1 (h u).2.2 P.Y (P.into u) :))
  bij := (by with_unfolding_all exact (fun u : D.what₂.Word => colDictBij_reTr Z (P.tr u) (h u).2.1 (h u).2.2 P.Y (P.bij u) :))
  lev := (by with_unfolding_all exact (fun u : D.what₂.Word => levelMatch_reTr Z (P.tr u) (h u).1 (h u).2.1 (h u).2.2 P.Y (P.lev u) :))
  isom := (by with_unfolding_all exact (fun u : D.what₂.Word => colDictIsom_reTr Z (P.tr u) (h u).2.1 (h u).2.2 P.Y P.fin hF (P.isom u) :))
  inst := (by with_unfolding_all exact (P.inst :))
  G := reG Z P.G
  pin := (by with_unfolding_all exact (P.pin :))

section API

variable {F : ∀ u, Forms0 D u} (P : SPack D F) {F' : ∀ u, Forms0 (reD D Z) u} (h : SameForms0LevelsAndValues Z F F') (hF : FinX (reY Z P.Y))

end API

theorem conjHH_eEECre {X : HidaSetting D} (G : GoodOp X) (x : EEC X G) :
    conjHH (reX Z X) (reG Z G) (eEECre Z G x) = eHHre Z X (conjHH X G x) := (by with_unfolding_all exact (Eq.refl (eHHre Z X (conjHH X G x)) :))

theorem exists_sameF_ofDiv (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (ht : D.what₂.Word → ℝ) (F : ∀ u, Forms0 D u) :
    ∃ F' : ∀ u, Forms0 (reD D (New.ofDiv D N ht)) u, SameForms0LevelsAndValues (New.ofDiv D N ht) F F' := by
  let G : ∀ u : D.what₂.Word, Forms0 (GlobalTheory.EX.OB.setDiv D N ht) u := fun u =>
    { F u with
      atT := { (F u).atT with }
      cls0 := { (F u).cls0 with }
      val0 := { (F u).val0 with }
      lv0 := { (F u).lv0 with } }
  refine ⟨(by with_unfolding_all exact (G :)), fun u => ⟨?_, ?_, ?_⟩⟩
  · exact (by with_unfolding_all exact (Eq.refl (F u).cls0.lev :))
  · exact (by with_unfolding_all exact (Eq.refl (F u).cls0.y :))
  · exact (by with_unfolding_all exact (Eq.refl (F u).val0.eY :))

end GlobalTheory.Mem.SRe

end
end

section

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

def PrePin (P : Pre) : Prop :=
  letI := P.host.cmStar; ∀ (a : Fin P.sp.X'.rank) (b : Fin (P.sp.X P.R.m).rank), (a : ℕ) = b →
    P.sp.iX' (P.sp.X'.frame a) = (P.sp.X P.R.m).frame b

def KPx : BaseP := fun B f => (∃ δ : Fld.FieldDat B.toPre, B.KsExact δ f) ∧ PrePin B.toPre

structure ColW (B : Base) (f : Fr B.toPre) (T : TwDat B) : Type 1 where
  px : PreX B.toPre
  I : ColIn B px
  ok : I.Ok
  C_eq : I.C = f
  S_eq : I.S = {p | p ∈ offSet B.toPre ∧ p ≠ B.host.pde ∧ p ≠ B.host.pde'}
  xi_range : Set.range I.xi = T.set f
  pins : TC.Pins B px
  l : TC.Laws I
  l0 : TC.Law0 I l
  δ : Fld.FieldDat B.toPre
  exact : B.KsExact δ f
  fld : GlobalTheory.Mem.Per.FieldOK B.host B.embLL B.embE
  val : ∀ C W V S N G, ValLL0 (assemble B C W V S N G) (Fr.at ⟨B, C, W, V, S, N, G⟩ f)

namespace ColW

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T)

abbrev C : Cols B := TC.cols w.I w.l

abbrev Lt : Type _ := TC.Later B w.C

abbrev st (Z : w.Lt) : Stages := ⟨B, w.C, Z.W, Z.V, Z.S, Z.N, Z.G⟩

abbrev D (Z : w.Lt) : D7 := TC.rec7 w.I w.l Z

abbrev tw (Z : w.Lt) : TwForms (w.D Z) := TC.tw w.I w.l w.l0 Z

end ColW

abbrev WP : Type 1 := ∀ (_ : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B), ColW B f T → Prop

abbrev ZP : Type 1 := ∀ (_ : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), w.Lt → Prop

abbrev CP : Type 1 :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt), V4.Core K (w.st Z) f T → Prop

def positionOf (P : CP) : V4.Slot := fun K X f T c =>
  ∃ (w : ColW X.B f T) (Z : w.Lt) (c' : V4.Core K (w.st Z) f T), P K X.B f T w Z c' ∧
    (⟨X.C, ⟨X.W, X.V, X.S, X.N, X.G⟩, c⟩ : Σ (C : Cols X.B) (Y : TC.Later X.B C), V4.Core K ⟨X.B, C, Y.W, Y.V, Y.S, Y.N, Y.G⟩ f T) =
      ⟨w.C, Z, c'⟩

def HasZ (P : ZP) : WP := fun K B f T w => ∃ Z : w.Lt, P K B f T w Z

def HasC (P : CP) : WP := fun K B f T w => ∃ (Z : w.Lt) (c : V4.Core K (w.st Z) f T), P K B f T w Z c

def StepW (p q : WP) : Prop :=
  Step KPx (fun _ _ _ _ => True) fun K B f T => ∀ w : ColW B f T, p K B f T w → q K B f T w

structure ColT {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) : Type 1 where
  C : Formalism.L2.Forms.ColsTiedSym (w.D Z)
  std : TC.StdC w.I w.l Z C
  stdLv : ∀ u, TC.StdLvC w.I w.l Z u (C.forms u)
  full : Formalism.L2.Forms.ColsFullS C
  stdDt : TC.StdDt w.I w.l Z full.1.base.dt
  Gt : GatTies (w.D Z)
  cmp : LatCmp (w.D Z)
  g : Formalism.L2.G.GroupCompatibilityAll (w.D Z) Gt cmp
  herm_eq : g.herm = full.1.to0
  forms_eq : g.forms = fun u => (C.forms u).to0
  gpl : Formalism.L2.Herm.SymmetricGroupCompatibleAtPlaces (w.D Z) full.1.base.toHermColsCh full.1.g Gt

theorem positionOf_intro {P : CP} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
    {c : V4.Core K (w.st Z) f T} (h : P K B f T w Z c) : positionOf P K (w.st Z) f T c := ⟨w, Z, c, h, rfl⟩

theorem positionOf_ind {P : CP} {R : V4.Slot}
    (h : ∀ K B f T (w : ColW B f T) (Z : w.Lt) (c : V4.Core K (w.st Z) f T), P K B f T w Z c → R K (w.st Z) f T c)
    {K : Ctx} {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B} {c : V4.Core K X f T} (hc : positionOf P K X f T c) : R K X f T c := by
  obtain ⟨B, C, W, V, S, N, G⟩ := X
  dsimp only at f T
  obtain ⟨w, Z, c', hp, e⟩ := hc
  exact Eq.mpr (congrArg (fun y : Σ (C : Cols B) (Y : TC.Later B C), V4.Core K ⟨B, C, Y.W, Y.V, Y.S, Y.N, Y.G⟩ f T =>
    R K ⟨B, y.1, y.2.1.W, y.2.1.V, y.2.1.S, y.2.1.N, y.2.1.G⟩ f T y.2.2) e) (h K B f T w Z c' hp)

theorem positionOf_mono {P P' : CP} (h : ∀ K B f T w Z c, P K B f T w Z c → P' K B f T w Z c) (K : Ctx) (X : Stages) (f : Fr X.B.toPre)
    (T : TwDat X.B) (c : V4.Core K X f T) (hc : positionOf P K X f T c) : positionOf P' K X f T c :=
  let ⟨w, Z, c', hp, e⟩ := hc; ⟨w, Z, c', h _ _ _ _ _ _ _ hp, e⟩

theorem StepW.of_all {p q : WP} (h : ∀ K B f T w, K.Over B.toPre → Forced K B T → p K B f T w → q K B f T w) : StepW p q :=
  Step.of_all fun K B f T a _ b _ w => h K B f T w a b

theorem StepW.trans {p q r : WP} (h : StepW p q) (h' : StepW q r) : StepW p r :=
  (Step.and h h').trans (Step.of_all fun _ _ _ _ _ _ _ H w a => H.2 w (H.1 w a))

theorem StepW.and {p q r : WP} (h : StepW p q) (h' : StepW p r) : StepW p fun K B f T w => q K B f T w ∧ r K B f T w :=
  (Step.and h h').trans (Step.of_all fun _ _ _ _ _ _ _ H w a => ⟨H.1 w a, H.2 w a⟩)

theorem step_hasCore {admitted : AtP} {p : WP} {P : CP} (h0 : Step KPx admitted fun K B f T => ∃ w : ColW B f T, p K B f T w)
    (h1 : StepW p (HasC P)) : Step KPx admitted (HasCore (positionOf P)) :=
  (h0.and ((Step.of_all fun _ _ _ _ _ _ _ _ => trivial).trans h1)).trans (Step.of_all fun _ _ _ _ _ _ _ H =>
    let ⟨w, a⟩ := H.1
    let ⟨Z, c, hc⟩ := H.2 w a
    ⟨w.C, Z.W, Z.V, Z.S, Z.N, Z.G, c, positionOf_intro hc⟩)

end GlobalTheory.Mem.Top.Bl

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Mem.R3.Res

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.FWT Formalism.L2.Pj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T T' : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {f : T' → T} {μ : T'}
  {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D (A.comap id (f μ)) C.Q.c.F}
  (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T') (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL)))



def omDat {i : Fin D.R.m} (O : OMDat C.toCore R i Unit fun _ => (A.comap id (f μ)).μ0) :
    OMDat C.toCore (dat2 f μ R mu tw) i Unit fun _ => (A.comap f μ).μ0 := { O with }



def fwTie {κ v₀} (t : FWTie C R κ v₀) : FWTie C (dat2 f μ R mu tw) κ v₀ :=
  { alg_eq := t.alg_eq, e := t.e, ks := t.ks, kap := t.kap, pt := t.pt, nrm_eq := t.nrm_eq, laws := t.laws, chiR := t.chiR,
    hv₀ := t.hv₀, x0 := t.x0, ev0 := t.ev0, ev := t.ev }



theorem omPins {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    (O : ∀ i, OMDat C.toCore R i Unit fun _ => (A.comap id (f μ)).μ0) (i : Fin D.R.m) (h : OMPins C R κ v₀ O i) :
    OMPins C (dat2 f μ R mu tw) κ v₀ (fun i => omDat mu tw (O i)) i := by
  refine ⟨h.1, ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h.2
  obtain ⟨g, c, l, ht, hb⟩ := h1.c0
  refine ⟨⟨h1.field, h1.std, ?_, ⟨g, c, l, ⟨ht.ranks, ht.v0, ht.tauL_ok, ht.pl_inj, ht.q, ht.S_fin, fun t => ht.ok (f t), ht.gramR_eq,
    ht.mapR, ht.mapL, fun t => ht.coefR (f t), fun i t => ht.coefL i (f t)⟩, hb⟩, h1.lev⟩, fun t => ⟨(h2 t).reps, (h2 t).B, (h2 t).xi, (h2 t).phi, (h2 t).half⟩,
    h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact h1.v0



def geoHalf {ph : Fin D.R.m → ℂ} (g : GlobalTheory.RealGeo.GeoHalf C R ph) : GlobalTheory.RealGeo.GeoHalf C (dat2 f μ R mu tw) ph :=
  ⟨g.κ, g.v₀, fwTie mu tw g.fw, g.bar, fun i => omDat mu tw (g.O i), fun i => omPins mu tw g.O i (g.pins i), g.rhoGeo, g.equivAll,
    g.cTie, g.phase⟩



theorem inGeo {ph : Fin D.R.m → ℂ} {g : GlobalTheory.RealGeo.GeoHalf C R ph} (h : GlobalTheory.RealGeo.InGeo g) :
    GlobalTheory.RealGeo.InGeo (geoHalf mu tw g) :=
  ⟨h.jEvExists, h.jEvBar, h.evInj, h.jUnif, h.geoAct, h.latFull, h.dimMatch⟩



theorem inGeo_iff {ph : Fin D.R.m → ℂ} {g : GlobalTheory.RealGeo.GeoHalf C R ph} :
    GlobalTheory.RealGeo.InGeo (geoHalf mu tw g) ↔ GlobalTheory.RealGeo.InGeo g :=
  ⟨fun h => ⟨h.jEvExists, h.jEvBar, h.evInj, h.jUnif, h.geoAct, h.latFull, h.dimMatch⟩, inGeo mu tw⟩

end GlobalTheory.Mem.R3.Res

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Mem.R3.Res

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T T' : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (f : T' → T) (μ : T')

def dat3 (R : RealDat3 D (A3.comap id (f μ)) Ks) (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T')
    (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) : RealDat3 D (A3.comap f μ) Ks where
  toRealDat := dat2 (A := A3.A) f μ R.toRealDat mu tw
  plI := R.plI
  SF := R.SF
  phs := R.phs
  lam3 i t := R.lam3 i (f t)

def bare3 (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G)
    (ψ1 : P1 →* D.what₂.LLˣ) : Face3 D A3 where
  P0 := P0
  ψ0 := ψ0
  P1 := P1
  ψ1 := ψ1
  Dc _ := ⟨PEmpty, fun u => u.elim, fun u => u.elim, fun u => u.elim⟩
  Sp _ := ⟨ℂ, inferInstance, inferInstance, fun u => u.elim, ⊥⟩
  Zsc _ := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

variable {f μ} {R : RealDat3 D (A3.comap id (f μ)) Ks} (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T')
  (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {P1 : Subgroup G} {ψ1 : P1 →* D.what₂.LLˣ}



theorem isInert (h : R.IsInert) : (dat3 f μ R mu tw).IsInert := by
  exact ⟨⟨h.tie.plI_inj, fun t Q => h.tie.okI (f t) Q⟩, h.onto, fun t => h.hR (f t), fun i t => h.hL i (f t), h.SF⟩



structure NewTup (R : RealDat3 D (A3.comap id (f μ)) Ks) (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T')
    (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) : Prop where

  sub : tw ⊆ R.twPl

  conj : ∀ w, Formalism.DivisionValues.conjPl w ∈ tw ↔ w ∈ tw

  on : ∀ w ∈ tw, f (mu w) = R.mu w

  off : ∀ w, w ∉ tw → mu w = μ

  used : ∀ t, t = μ ∨ ∃ w, mu w = t


variable {mu tw} in
theorem isTup (hf : Function.Injective f) (h : R.IsTup) (n : NewTup R mu tw) : (dat3 f μ R mu tw).IsTup := by
  constructor
  case mu_off => exact n.off
  case mu_used => exact n.used
  case mu_ne =>
    intro w hw heq
    change mu w = μ at heq
    apply h.mu_ne w (n.sub hw)
    rw [← n.on w hw, heq]
    rfl
  case mu_conj =>
    intro w
    change mu (Formalism.DivisionValues.conjPl w) = mu w
    by_cases hw : w ∈ tw
    · apply hf
      have hc : Formalism.DivisionValues.conjPl w ∈ tw := (n.conj w).2 hw
      rw [n.on _ hc, n.on w hw]
      exact h.mu_conj w
    · have hc : Formalism.DivisionValues.conjPl w ∉ tw := fun hc => hw ((n.conj w).1 hc)
      rw [n.off _ hc, n.off w hw]
  case mu_on =>
    intro w hw
    obtain ⟨ψw, Qw, h1, h2⟩ := h.mu_on w (n.sub hw)
    refine ⟨ψw, Qw, h1, ?_⟩
    change R.xiH (f (mu w)) = R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w) * ψw
    rw [n.on w hw]
    exact h2




theorem keep {cG : G0 R.Pg D.R.r ≃* G0g D.nd} (h : Keep (A3 := A3.comap id (f μ)) R.toRealDat (bare3 _ P0 ψ0 P1 ψ1).lv2 cG) :
    Keep (A3 := A3.comap f μ) (dat3 f μ R mu tw).toRealDat (bare3 _ P0 ψ0 P1 ψ1).lv2 cG := by
  constructor
  case std => exact h.std
  case signs => exact h.signs
  case frames => exact h.frames
  case beta => exact h.beta
  case prX => exact h.prX
  case grp => exact h.grp
  case psi => exact h.psi
  case guard => exact ⟨fun t => h.guard.1 (f t), fun t => h.guard.2 (f t)⟩
  case valKs => exact h.valKs
  case frameKs => exact h.frameKs
  case levKs => exact h.levKs


end GlobalTheory.Mem.R3.Res

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Col Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
open GlobalTheory.Mem GlobalTheory.Mem.Col2
open scoped TensorProduct

namespace GlobalTheory.Mem.R3

def MatEq {A : Type} [CommRing A] {a b : ℕ} (x : GL (Fin a) A) (y : GL (Fin b) A) : Prop :=
  a = b ∧ ∀ (i j : Fin a) (i' j' : Fin b), (i : ℕ) = i' → (j : ℕ) = j' → x.1 i j = y.1 i' j'

section Gen

variable {X : Fields} {n : ℕ} [NeZero n] {a : ℕ} {H Γ W : Type} [AddCommGroup W] [Module ℂ W] (σ : X.K →+* ℂ)
  (mat : H → GL (Fin a) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) (rat : Γ → GL (Fin a) X.E → Prop) (ρ : Γ → W → W)

def StdSide {ι : Type} (lam : X.Tau → DomWeight n) (rho : GL (Fin n) X.E →* Module.End X.K (VV X.K lam))
    (SG : ι → Finset (Pl X.E)) (Fm : ι → Type) (val : ∀ t, Fm t → DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG t) → VV X.K lam)
    (ad : ∀ t, Fm t → H → W) : Prop :=
  ∃ c : VV X.K lam →ₛₗ[σ] W,
    (∀ γ γE g, rat γ γE → MatEq γE g → ∀ v, c (rho g v) = ρ γ (c v)) ∧
    (∀ (hc : CMData X.F X.E) t (φ : Fm t) (h : H) (x : Formalism.L2.Col.UAd hc n), MatEq (mat h) (x : GL (Fin n) _) →
      ad t φ h = c (val t φ (decoPt hc n ∅ (SG t) (QuotientGroup.mk x)))) ∧
    (LinearIndependent ℂ fun i => c (bVV X.K lam i)) ∧
    ∃ hc : CMData X.F X.E, ∀ h : H, ∃ x : Formalism.L2.Col.UAd hc n, MatEq (mat h) (x : GL (Fin n) _)

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def matIn {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (h : Bridge.Gf V) : GL (Fin V.rank) (Lev.EAf D) :=
  Formalism.UG.bc (swapAE D) (h : GL (Fin V.rank) _) * β

variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL))
  (tr : TrI X.B px)



def BrgStdR (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (cX : CoefA X.toD7.sp.X')
    (jR : ∀ t, (famR X I hX U Xg tr).A.fam.amb.FR t → Bridge.Gf X.toD7.sp.X' → cX.W) : Prop :=
  StdSide (X := X.B.fields) (n := X.B.R.N X.B.R.m - 1) (a := X.toD7.sp.X'.rank) (H := Bridge.Gf X.toD7.sp.X') (Γ := GQ X.toD7.sp.X')
    (W := cX.W) ((X.B.embLL)) ((matIn X.toD7.sp.X' L.βX)) ((Bridge.IsRatMat X.toD7.sp.X'))
    (fun γ v => cX.coef.ρ γ v) (ι := TupU I U) X.B.wts.sgTrue (rhoV X.B.fields.emb X.B.wts.sgTrue)
    (fun t => rowSG (X.B.primes px) I.sel t.1)
    (fun t => PLift (mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).Ok ×
      (mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).EqFun)
    (fun _ φ => φ.2.1)
    fun t φ => jR t ((by with_unfolding_all exact ((mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).res φ.1.down φ.2 :)))



def BrgStdV (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (i : Fin X.toD7.R.m) (cV : CoefA (Vc X.toD7 i))
    (jL : ∀ t, (famR X I hX U Xg tr).A.fam.amb.FL i t → Bridge.Gf (Vc X.toD7 i) → cV.W) : Prop :=
  StdSide (X := X.B.fields) (n := X.B.R.nV) (a := (Vc X.toD7 i).rank) (H := Bridge.Gf (Vc X.toD7 i)) (Γ := GQ (Vc X.toD7 i))
    (W := cV.W) ((X.B.embLL)) ((matIn (Vc X.toD7 i) (L.βV i))) ((Bridge.IsRatMat (Vc X.toD7 i)))
    (fun γ v => cV.coef.ρ γ v) (ι := TupU I U) (X.B.wts.lamV ((i : ℕ) + 1)) (rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1)))
    (fun t => rowSG (X.B.primes px) I.sel t.1)
    (fun t => PLift (mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).Ok ×
      (mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).EqFun)
    (fun _ φ => φ.2.1)
    fun t φ => jL t ((by with_unfolding_all exact ((mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res φ.1.down φ.2 :)))

def BrgStd {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks X.toD7.what₂.LL] (R : RealDat X.toD7 (famR X I hX U Xg tr).A Ks) : Prop :=
  BrgStdR X I hX U Xg tr R.toLevCh R.cX (fun t φ => R.B.jR t φ) ∧
    ∀ i, BrgStdV X I hX U Xg tr R.toLevCh i (R.cV i) fun t φ => R.B.jL i t φ


variable {X I hX} in
def Dat.Std {T : Top.TwDat X.B} {Wt : Set X.B.places.Pl} (z : Dat X I hX T Wt) : Prop :=
  BrgStd X I hX (usedOf I T Wt) z.Xg z.tr z.R.toRealDat

end GlobalTheory.Mem.R3

end
end
