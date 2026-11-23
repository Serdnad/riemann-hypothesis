module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle592
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle514
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle553
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SecondStepNoFormsOutsideLiftRange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle591
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralShiftExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1650
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle237
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting.Up GlobalTheory.Mem.R3.Tr



namespace GlobalTheory.HeightCounting.SerCopy

def lamT {D : D7} (N : TwNew D) (Z : GlobalTheory.LamTie.LamDat D) : GlobalTheory.LamTie.LamDat N.toD7 := ⟨N.cf Z.C, Z.q0, Z.w0, Z.c, Z.chi⟩

theorem lamT_spec {D : D7} (N : TwNew D) {cf : CharFrame D} {Z : GlobalTheory.LamTie.LamDat D}
    (h : Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D ∧ GlobalTheory.LamTie.IsLamTieFull N.tw Z) :
    (lamT N Z).Ok ∧ (lamT N Z).Teich ∧ (lamT N Z).C = N.cf cf ∧ (lamT N Z).q0 = AbsolutelyIrreducibleSpan.q0 N.toD7 ∧
      GlobalTheory.LamTie.IsLamTieFull N.toD7.ntw (lamT N Z) :=
  ⟨⟨(by with_unfolding_all exact (h.1.places :)), (by with_unfolding_all exact (h.1.aux :)), (by with_unfolding_all exact (h.1.big :))⟩, (by with_unfolding_all exact (h.2.1 :)), congrArg N.cf h.2.2.1, (by with_unfolding_all exact (h.2.2.2.1 :)), (by with_unfolding_all exact (h.2.2.2.2 :))⟩

theorem exists_prepared (hA : GlobalTheory.Published.GlobalArtinReciprocity) {D : D7} {cf : CharFrame D} {Rw : RowSide D} {low : Finset ℕ}
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S : RatDat D.ntw}
    {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0}
    {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ} (Bs : SideB D cf Rw low Pq S hL eig θ) (hV : ValLL0 D cf)
    (hr : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) :
    ∃ N : TwNew D, (∀ Z : GlobalTheory.LamTie.LamDat D, GlobalTheory.LamTie.IsLamTieFull D.ntw Z → GlobalTheory.LamTie.IsLamTieFull N.tw Z) ∧
      (∀ i', ∃ i, N.tw.S0 i' = D.ntw.S0 i ∧ N.tw.l i' = D.ntw.l i) ∧ NoOff N.toD7 ∧ GlobalTheory.UnivChar.IsUnivChar N.toD7.nexp ∧
      ∃ Bs' : SideB N.toD7 (N.cf cf) (N.row Rw) low Pq (N.rat S) hL eig θ, TauTrue Bs'.exp := by
  obtain ⟨N, h1, h2, h3, ⟨B1⟩⟩ := GlobalTheory.T.secondStep_no_forms_outside_liftRange D cf Rw low Pq S hL eig θ Bs
  obtain ⟨τ, hτ⟩ := GlobalTheory.TwInputs.exists_tau_family hA N.toD7 _ _ _ _ _ _ _ _ B1
    ⟨(by with_unfolding_all exact (hV.mu0 :)), (by with_unfolding_all exact (hV.eta :)), (by with_unfolding_all exact (hV.chiPsi :)), (by with_unfolding_all exact (hV.del :)), (by with_unfolding_all exact (hV.del' :))⟩ ((by with_unfolding_all exact (hr :)))
  obtain ⟨⟨tw, ex, h0, th, br, hbr⟩, e, g1, g2, B2, g3⟩ := GlobalTheory.T.exists_twistData_lowerBlock_universalCharacter N.toD7 _ _ _ _ _ _ _ _ B1 τ hτ
  dsimp only at e
  subst e
  exact ⟨⟨N.tw, (by with_unfolding_all exact (ex :)), (by with_unfolding_all exact (h0 :)), (by with_unfolding_all exact (th :)), (by with_unfolding_all exact (br :)), (by with_unfolding_all exact (hbr :))⟩, h1, h2, (by with_unfolding_all exact ((g1 h3) :)), (by with_unfolding_all exact (g2 :)), (by with_unfolding_all exact (B2 :)), (by with_unfolding_all exact (g3 :))⟩

theorem sideB_tau_congr {D : D7} {cf cf' : CharFrame D} {Rw : RowSide D} {low : Finset ℕ}
    {Pq Pq' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S S' : RatDat D.ntw}
    {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {hL' : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S'.WL j)}
    {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0} {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ}
    (e1 : cf = cf') (e4 : Pq = Pq') (e5 : S = S') (e6 : HEq hL hL')
    (h : ∃ Bs : SideB D cf Rw low Pq S hL eig θ, TauTrue Bs.exp) : ∃ Bs : SideB D cf' Rw low Pq' S' hL' eig θ, TauTrue Bs.exp := by
  subst e1 e4 e5
  cases e6
  exact h

variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

def PreAt {Z : w.Lt} (z : Dat (w.st Z) w.I P.hX T P.Wt) (Rw : RowSide (w.st Z).toD7)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (w.st Z).toD7.host.E)) → PlE (w.st Z).toD7.host) {α : Type} (h₀ : α)
    (eig : ℕ → (w.st Z).toD7.what₂.FT → ℕ → PlE (w.st Z).toD7.host → ↥(w.st Z).toD7.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((w.st Z).toD7.host.g kk)) →* (↥(w.st Z).toD7.LL0)ˣ) : Prop :=
  z.R.C = TC.cf w.I w.l Z ∧ ∃ kKs hk hL, HEq hL h₀ ∧
    ∃ (Bs : SideB (w.st Z).toD7 z.R.C Rw (lowAll (w.st Z).toD7) Pq (ratDatR z.R z.cG kKs hk) hL eig θ) (hF : _),
      TauTrue Bs.exp ∧ Nonempty (PreTie (ysOf Bs) z.geo.v₀ Bs.exp hF Pq)

theorem preAt_congr {Z : w.Lt} {z z' : Dat (w.st Z) w.I P.hX T P.Wt} {Rw Rw' Pq Pq'} {α α' : Type} {h₀ : α} {h₀' : α'}
    {eig eig' θ θ'} (e0 : z = z') (e1 : Rw = Rw') (e2 : Pq = Pq') (e3 : HEq h₀ h₀') (e4 : eig = eig') (e5 : θ = θ')
    (h : PreAt (P := P) z Rw Pq h₀ eig θ) : PreAt (P := P) z' Rw' Pq' h₀' eig' θ' := by
  subst e0 e1 e2 e4 e5
  obtain ⟨g1, k, hk, hf, g2, g3⟩ := h
  exact ⟨g1, k, hk, hf, g2.trans e3, g3⟩

section Install

variable {x : St P} {N₁ : TwNew (Dof x)}
  {kKs : (Up.datTw x N₁).core.Q.c.F →+* ↥(DN x N₁).LL0}
  {hk : ∀ y : (Up.datTw x N₁).core.Q.c.F,
    ((kKs y : ↥(DN x N₁).LL0) : (DN x N₁).what₂.LL) =
      algebraMap (Up.datTw x N₁).core.Q.c.F (DN x N₁).what₂.LL y}
  {cf : CharFrame (DN x N₁)} {Rw : RowSide (DN x N₁)}
  {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (DN x N₁).host.E)) → PlE (DN x N₁).host}
  {hf : ∀ j, ℕ → PlE (DN x N₁).host →
    Module.End (DN x N₁).what₂.LL ((ratDatR (Up.datTw x N₁).R (Up.datTw x N₁).cG kKs hk).WL j)}
  {eig : ℕ → (DN x N₁).what₂.FT → ℕ → PlE (DN x N₁).host → ↥(DN x N₁).LL0}
  {θ : ∀ kk : Fin 2, Multiplicative (ZMod ((DN x N₁).host.g kk)) →* (↥(DN x N₁).LL0)ˣ}
  {Bs : SideB (DN x N₁) cf Rw (lowAll (DN x N₁)) Pq
    (ratDatR (Up.datTw x N₁).R (Up.datTw x N₁).cG kKs hk) hf eig θ}
  {hF : (DN x N₁).host.F = maximalRealSubfield (DN x N₁).host.E}

abbrev kwP (p : PreTie (ysOf Bs) (Up.datTw x N₁).geo.v₀ Bs.exp hF Pq) : TwNew (DN x N₁) :=
  keepTw (DN x N₁) p.Dat (PreTie.th (D := DN x N₁) p) p.lev p.thPsi p.h1 p.thU p.thP p.MtLat p.h2 p.h3 p.nth

def bsP (p : PreTie (ysOf Bs) (Up.datTw x N₁).geo.v₀ Bs.exp hF Pq) :
    SideB (kwP p).toD7 ((kwP p).cf cf) ((kwP p).row Rw)
      (lowAll (DN x (SerCopy.nP p))) Pq
      ((kwP p).rat (ratDatR (Up.datTw x N₁).R (Up.datTw x N₁).cG kKs hk)) hf eig θ := by
    exact keepSideB (DN x N₁) p.Dat (PreTie.th (D := DN x N₁) p) p.lev p.thPsi
      p.h1 p.thU p.thP p.MtLat p.h2 p.h3 p.nth p.hU cf Rw _ Pq _ hf eig θ Bs

end Install


end GlobalTheory.HeightCounting.SerCopy

end
end

section

noncomputable section

namespace GlobalTheory.HeightCounting.Fin3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar




variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
  {x : St P} (l : LC hL x)

theorem mtIn : MtInput (Dof x) l.mt.M l.c.tp.tup l.c.ch.Q := by
  have h := congrArg₂
    (fun (ξ : (Dof x).what₂.Tup → HChar (Dof x).host.E) Q =>
      MtInput (Dof x) l.mt.M (fun μ j => (cfOf x).mu0 j * ξ μ) Q)
    l.c.xi_eq l.c.Q_eq
  exact h.mpr l.mt.mt

variable {big : (Dof x).what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 (Dof x))} (Sp : NdSpec l.a.A.pl l.mt.M l.c.ch big L.X L.T)
  (Au : AutSpec l.a.A l.mt.M l.c.tp.tup Sp.iq L.Y L.C) (ss : ∀ σ lam, IsSSRep (L.Z.rbar σ lam))

def ntW : NTrue hL (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp) :=
  { D := Dof x, cf := cfOf x, jE := l.a.jE, A := l.a.A, cg := l.a.cg, au := l.a.au, rep := repOf x.r.Y, row := l.a.row
    low := lowAll (Dof x), Pq := l.Pq, S := l.rat.S, hL := l.rat.In.hL, eig := l.rat.In.eig, θ := l.rat.In.θ, Bs := l.b.Bs
    M := l.mt.M, C := l.c.ch, tp := l.c.tp, ch := l.c.side, mt := mtIn l, big := big, L := L, Sp := Sp, Au := Au, ss := ss
    eq := rfl, pack := rfl }


variable (L) in
structure AllL : Type 1 where
  a : NAllC (withLoc L) (chL L l.c.ch)
  chr : (⟨a.cf, a.tp⟩ : Σ c : CharFrame (withLoc L), TupTied (withLoc L) c (chL L l.c.ch)) = ⟨cfL L (cfOf x), tpL L l.c.tp⟩
  jE : a.gal.fr.jE = l.a.jE
  mt : a.gal.mt = mtL L l.mt.M
  exp : ExpRel L l.b.Bs.exp a.exp
  chrN : NCharTied (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp)
  chrGal : NGalChrTied (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp)
  loc : ∀ F : Formalism.L2.RowFrame (withLoc L), F.rep = repOf x.r.Y → Formalism.L2.RowLocTied (withLoc L) a.gal.lp F


theorem low_ok (D : D7) : 2 ∈ lowAll D ∧ AbsolutelyIrreducibleSpan.q0 D ∈ lowAll D ∧ (NumberField.discr D.host.E).natAbs.primeFactors ⊆ lowAll D ∧
    (Ideal.absNorm D.host.ccK).primeFactors ⊆ lowAll D := by
  have memLow {p : ℕ} (hp : p ∈ Formalism.L2.lowPr D) : p ∈ lowAll D :=
    Finset.mem_union_left _ hp
  have memPrimes {p : ℕ} (hp : p ∈ (Ideal.absNorm D.host.ccK).primeFactors ∪
      (NumberField.discr D.host.E).natAbs.primeFactors) : p ∈ lowAll D :=
    memLow (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hp))
  exact ⟨memLow (Finset.mem_insert_self _ _),
    memLow (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)),
    fun _ hp => memPrimes (Finset.mem_union_right _ hp),
    fun _ hp => memPrimes (Finset.mem_union_left _ hp)⟩

private theorem admTw_of_withLoc {D : D7} {L : LocAll (lay0 D)} {i k Q ψ}
    (h : Formalism.L2.NX.AdmTw (withLoc L) i k Q ψ) : Formalism.L2.NX.AdmTw D i k Q ψ := by
  unfold Formalism.L2.NX.AdmTw at h ⊢
  with_unfolding_all exact h

variable (al : AllL l L) (hLg : GlobalTheory.CoefDuty.Large (withLoc L))

theorem pqW (i j b k Q ψ) (h1 : 1 ≤ j) (h2 : j ≤ (withLoc L).R.m) (hadm : Formalism.L2.NX.AdmTw (withLoc L) i k Q ψ) :
    plsOf al.a.exp i j b k Q ψ h1 h2 hadm = (qpOf (Dof x) l.Pq Q, qpOf (Dof x) l.Pq ((Dof x).ntw.pD i)) := by
  have hpl := al.exp.pl i j b k Q ψ h1 h2 hadm
  have hadm₀ := admTw_of_withLoc (D := Dof x) (L := L) hadm
  have hpq := l.b.Bs.pq i j b k Q ψ h1 h2 hadm₀
  have hpair := congrArg₂ Prod.mk hpq.1 hpq.2
  with_unfolding_all exact (hpl.trans hpair :)

def natW : NAt hL (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp) where
  nt := ntW l Sp Au ss
  all := al.a
  chr_eq := al.chr
  host := ⟨(by with_unfolding_all exact (l.a.host.fr :)), (by with_unfolding_all exact (l.a.host.jLL :)), (by with_unfolding_all exact (l.a.host.embLL :))⟩
  frameN := by
    intro y
    with_unfolding_all exact (RingHom.congr_fun al.jE y).trans (l.a.frame y)
  chrN := al.chrN
  chrGal := al.chrGal
  Pq := (by with_unfolding_all exact (l.Pq :))
  Pq_over := (by with_unfolding_all exact (l.Pq_over :))
  pq := fun i j b k Q ψ h1 h2 hadm => ⟨(by with_unfolding_all exact ((congrArg Prod.fst (pqW l al i j b k Q ψ h1 h2 hadm)) :)),
    (by with_unfolding_all exact ((congrArg Prod.snd (pqW l al i j b k Q ψ h1 h2 hadm)) :))⟩
  jE_eq := (by with_unfolding_all exact ((heq_of_eq al.jE.symm) :))
  mt_eq := (by with_unfolding_all exact ((heq_of_eq al.mt.symm) :))
  Pq_eq := (by with_unfolding_all exact ((HEq.refl l.Pq) :))
  low := (by with_unfolding_all exact ((low_ok (Dof x)) :))
  split := hLg.2.1
  ratIn := l.rat.In
  ratIn_hL := rfl
  ratIn_eig := rfl
  ratIn_θ := rfl
  depth := l.a.depth

abbrev PackedNAt (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) :=
  Σ (cf : CharFrame D) (c : NChoice D) (tp : TupTied D cf c), NAt hL D cf c tp

-- Transport the character data and the record together so their indices stay aligned.
def natDData : PackedNAt hL (DL x L) :=
  Eq.rec (motive := fun D _ => PackedNAt hL D)
    ⟨cfL L (cfOf x), chL L l.c.ch, tpL L l.c.tp, natW l Sp Au ss al hLg⟩ (DL_eq x L).symm

abbrev natD := (natDData l Sp Au ss al hLg).2.2.2

theorem packedNAt_transport_heq {D D' : D7} (e : D = D') (a : PackedNAt hL D) :
    let b : PackedNAt hL D' := Eq.rec (motive := fun d _ => PackedNAt hL d) a e
    HEq (ratL b.2.2.2.nt.L b.2.2.2.nt.S) (ratL a.2.2.2.nt.L a.2.2.2.nt.S) ∧
      HEq b.2.2.2.nt.hL a.2.2.2.nt.hL ∧ HEq b.2.2.2.nt.rep a.2.2.2.nt.rep := by
  cases e
  exact ⟨HEq.refl _, HEq.refl _, HEq.refl _⟩

theorem natD_heq :
    HEq (ratL (natD l Sp Au ss al hLg).nt.L (natD l Sp Au ss al hLg).nt.S) (ratL L l.rat.S) ∧
      HEq (natD l Sp Au ss al hLg).nt.hL l.rat.In.hL ∧
      HEq (natD l Sp Au ss al hLg).nt.rep (repOf x.r.Y) := by
  let a : PackedNAt hL (withLoc L) :=
    ⟨cfL L (cfOf x), chL L l.c.ch, tpL L l.c.tp, natW l Sp Au ss al hLg⟩
  have h := packedNAt_transport_heq (D := withLoc L) (D' := DL x L) (DL_eq x L).symm a
  dsimp only [natD, natDData, natW, ntW, a] at h ⊢
  exact h


include l in
variable (L) in
theorem grpD : Formalism.L2.DIV.GrpTie (DL x L) (famR (w.st (oL x L).Z) w.I P.hX (usedOf w.I T P.Wt) (datL x L).Xg (datL x L).tr).A
    (datL x L).F.P0 (datL x L).F.ψ0 (datL x L).F.P1 (datL x L).F.ψ1 ((datL x L).R.eG.trans (datL x L).cG) :=
  ⟨(by with_unfolding_all exact ((GlobalTheory.T.group_tie_of_local_coefficient l).card :)), (by with_unfolding_all exact ((GlobalTheory.T.group_tie_of_local_coefficient l).e0 :)), (by with_unfolding_all exact ((GlobalTheory.T.group_tie_of_local_coefficient l).lvl0 :)), (by with_unfolding_all exact ((GlobalTheory.T.group_tie_of_local_coefficient l).psi0 :)), (by with_unfolding_all exact ((GlobalTheory.T.group_tie_of_local_coefficient l).idxSharp :)),
    (datL x L).pins.keep.psi.lvl⟩

variable {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0) (hY : YRel L Y)

def frameY : Formalism.L2.RowFrame (DL x L) := Formalism.L2.Col.rowFrameOf (DL x L) _ Y.eFT

def rowD : NRow (D := DL x L) (natD l Sp Au ss al hLg) (datL x L).R (datL x L).F (datL x L).cG Y where
  kKs := kKsL L l.rat
  hk := hkL L l.rat
  nexp := ysL L l
  hecke := hkHL L l
  grp := grpD l L
  rowLoc := by
    let F : Formalism.L2.RowFrame (withLoc L) :=
      ⟨(frameY Y).rep, (frameY Y).inj⟩
    have hF : F.rep = repOf x.r.Y := by
      with_unfolding_all exact eq_of_heq hY.rep
    exact ⟨by with_unfolding_all exact ((al.loc F hF).sat :)⟩
  S_eq := (natD_heq l Sp Au ss al hLg).1.trans (SL_heq L l.rat)
  hL_eq := by with_unfolding_all exact ((natD_heq l Sp Au ss al hLg).2.1 :)
  rep_eq := by with_unfolding_all exact ((natD_heq l Sp Au ss al hLg).2.2.trans hY.rep.symm :)



def RowsAt (P : Pre2 K w) : Prop := ∀ x : St P, (∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v) →
  ∃ t : RowsT K w x.o.Z P.Wt x.s.p0, Nonempty (RXs t) ∧ t.hX = P.hX ∧ HEq t.r.z x.m.z ∧ HEq t.r.Y x.r.Y ∧ HEq t.r.Z.jW x.r.Z.jW




end GlobalTheory.HeightCounting.Fin3

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeCharacterRestriction

variable {D : D7}

section Chars

variable {T : Type} {L : LevCh D T} {μ0 : T}

theorem isHecke_mu (hL : L.Is μ0) (t : T) (j : Fin D.R.m) : IsHeckeChar D (L.mu t ((j : ℕ) + 1)) :=
  ⟨(hL.mu0 j).1.1.mul (hL.xi t).1.1, fun x =>
    (congrArg₂ (· * ·) ((hL.mu0 j).1.2 x) ((hL.xi t).1.2 x)).trans (mul_one _)⟩

theorem resEta_mu (hL : L.Is μ0) (t : T) (j : Fin D.R.m) : ResEta D (L.mu t ((j : ℕ) + 1)) 0 := by
  have hres := GlobalTheory.Mem.EtaTilde.isEta_res D L.eta L.C.eta hL.eta L.C.isEta
  refine ⟨⟨_, hres⟩, fun η _ a => ?_⟩
  show L.mu0 ((j : ℕ) + 1) (idF D a) * L.xi t (idF D a) = _
  rw [pow_zero, GlobalTheory.GridWeil.triv_base (hL.mu0 j) (L.C.isMu0 j).triv a, GlobalTheory.GridWeil.triv_base (hL.xi t) (hL.xi_triv t) a, mul_one]

theorem resEta_eta (hL : L.Is μ0) : ResEta D L.eta 1 := by
  have hres := GlobalTheory.Mem.EtaTilde.isEta_res D L.eta L.C.eta hL.eta L.C.isEta
  refine ⟨⟨_, hres⟩, fun η h a => ?_⟩
  rw [(GlobalTheory.IdeleNormChar.existsUnique_isEta D).unique h hres, pow_one, MonoidHom.comp_apply]

theorem isHecke_quot (hL : L.Is μ0) (t : T) (j : Fin D.R.m) : IsHeckeChar D (L.mu t ((j : ℕ) + 1) * L.eta⁻¹) :=
  ⟨(isHecke_mu hL t j).1.mul (hL.eta.1.1.inv), fun x => by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, (isHecke_mu hL t j).2, hL.eta.1.2, inv_one, mul_one]⟩

theorem resEta_quot (hL : L.Is μ0) (t : T) (j : Fin D.R.m) {n : ℕ} (hn : Odd n) :
    ResEta D (L.mu t ((j : ℕ) + 1) * L.eta⁻¹) n :=
  resEta_parity (resEta_mul (resEta_mu hL t j) (resEta_inv (resEta_eta hL)))
    (by obtain ⟨c, rfl⟩ := hn; omega)

theorem resEta_even (hL : L.Is μ0) (t : T) (j : Fin D.R.m) {n : ℕ} (hn : Even n) :
    ResEta D (L.mu t ((j : ℕ) + 1)) n :=
  resEta_parity (resEta_mu hL t j) (by obtain ⟨c, rfl⟩ := hn; omega)

theorem odd_r : Odd D.R.r := by
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have := D.R.two_le_m
  refine ⟨a + b - 1, ?_⟩
  unfold Ranks.r
  omega

theorem even_rankY (j : ℕ) : Even (D.R.rankY j) ↔ ¬ Even j := by
  have h1 : ¬ Even D.R.r := Nat.not_even_iff_odd.2 odd_r
  have h2 : ¬ Even D.R.t := Nat.not_even_iff_odd.2 D.R.t_odd
  unfold Ranks.rankY
  rw [Nat.even_add, Nat.even_mul]
  tauto

theorem rank_Yc {k : ℕ} (h : k ≤ D.R.m) : (Yc D k).rank = D.R.rankY k := by
  show (D.sp.Y (min k D.R.m)).rank = _
  rw [min_eq_left h]
  exact D.sp.Y_rank k h

theorem step_facts (hL : L.Is μ0) (t : T) (j : Fin D.R.m) {a b : ℕ} (ha : Even a ↔ ¬ Even (j : ℕ)) (hb : Even b ↔ Even (j : ℕ)) :
    IsHeckeChar D (Lift.chrStep (L.mu t) L.eta ((j : ℕ) + 1)).1 ∧ IsHeckeChar D (Lift.chrStep (L.mu t) L.eta ((j : ℕ) + 1)).2 ∧
      ResEta D (Lift.chrStep (L.mu t) L.eta ((j : ℕ) + 1)).1 a ∧ ResEta D (Lift.chrStep (L.mu t) L.eta ((j : ℕ) + 1)).2 b := by
  unfold Lift.chrStep
  by_cases h : Even (j : ℕ)
  · rw [if_pos h.add_one]
    exact ⟨isHecke_quot hL t j, isHecke_mu hL t j,
      resEta_quot hL t j (Nat.not_even_iff_odd.1 fun e => ha.1 e h), resEta_even hL t j (hb.2 h)⟩
  · rw [if_neg (fun e => h (by simpa [Nat.odd_add_one] using e))]
    exact ⟨isHecke_mu hL t j, isHecke_quot hL t j, resEta_even hL t j (ha.2 h),
      resEta_quot hL t j (Nat.not_even_iff_odd.1 fun e => h (hb.1 e))⟩

theorem splitFacts (hL : L.Is μ0) (t : T) :
    (∀ k, k + 1 < D.R.m → IsHeckeChar D (Lift.chrStep (L.mu t) L.eta (k + 1)).1 ∧
      IsHeckeChar D (Lift.chrStep (L.mu t) L.eta (k + 1)).2 ∧
      ResEta D (Lift.chrStep (L.mu t) L.eta (k + 1)).1 (Yc D k).rank ∧
      ResEta D (Lift.chrStep (L.mu t) L.eta (k + 1)).2 (Yc D (k + 1)).rank) ∧
    (IsHeckeChar D (Lift.chrStep (L.mu t) L.eta D.R.m).1 ∧ IsHeckeChar D (Lift.chrStep (L.mu t) L.eta D.R.m).2 ∧
      ResEta D (Lift.chrStep (L.mu t) L.eta D.R.m).1 (Yc D (D.R.m - 1)).rank ∧
      ResEta D (Lift.chrStep (L.mu t) L.eta D.R.m).2 D.sp.X'.rank) ∧
    ∀ i : Fin D.R.m, IsHeckeChar D (Lift.chrTh (L.mu t) L.eta ((i : ℕ) + 1)).1 ∧
      IsHeckeChar D (Lift.chrTh (L.mu t) L.eta ((i : ℕ) + 1)).2 ∧
      ResEta D (Lift.chrTh (L.mu t) L.eta ((i : ℕ) + 1)).1 (Vc D i).rank ∧
      ResEta D (Lift.chrTh (L.mu t) L.eta ((i : ℕ) + 1)).2 (Wc D i).rank := by
  have hm2 := D.R.two_le_m
  refine ⟨fun k hk => ?_, ?_, fun i => ?_⟩
  · refine step_facts hL t ⟨k, by omega⟩ (a := (Yc D k).rank) (b := (Yc D (k + 1)).rank) ?_ ?_
    · rw [rank_Yc (by omega)]; exact even_rankY k
    · rw [rank_Yc (by omega), even_rankY]
      show _ ↔ Even k
      rw [Nat.even_add_one, not_not]
  · have hj : D.R.m - 1 < D.R.m := by omega
    have e : D.R.m - 1 + 1 = D.R.m := by omega
    have hne : ¬ Even (D.R.m - 1) := fun h => by
      have := h.add_one
      rw [e] at this
      exact (Nat.not_odd_iff_even.2 D.R.m_even) this
    have key := step_facts hL t ⟨D.R.m - 1, hj⟩ (a := (Yc D (D.R.m - 1)).rank) (b := D.sp.X'.rank)
      (by rw [rank_Yc (by omega)]; exact even_rankY _)
      (by
        rw [D.sp.X'_rank]
        show Even (D.R.rankY D.R.m) ↔ Even (D.R.m - 1)
        rw [even_rankY]
        exact iff_of_false (not_not.2 D.R.m_even) hne)
    simpa only [e] using key
  · have hV : (Vc D i).rank = D.R.nV := D.sp.V_rank _ (by omega) (by omega)
    have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (by omega) (by omega)
    refine ⟨isHecke_mu hL t i, isHecke_quot hL t i, resEta_even hL t i ?_, resEta_quot hL t i ?_⟩
    · rw [hV]
      exact odd_r.add_odd D.R.t_odd
    · rw [hW]
      exact odd_r

end Chars

section Places

variable {T : Type} {L : LevCh D T} {μ0 : T}

theorem not_isConjPl_union (hL : L.Is μ0) (t : T) {P P' : Pl D.host.E} (h : P ∈ L.Pg ∨ P ∈ L.Q t)
    (h' : P' ∈ L.Pg ∨ P' ∈ L.Q t) : ¬ Lev.IsConjPl P P' := by
  rcases h with h | h
  · exact (GlobalTheory.ChainEquiv.places_sep L μ0 hL t).1 P h P' h'
  · rcases h' with h' | h'
    · intro hc
      obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hL.Q_pl t P h
      obtain ⟨k, hk⟩ := (hL.Pg P').1 h'
      have h1 : (q : 𝓞 D.host.E) ∈ P.asIdeal := by
        have hzero : Nat.card (kP P) • (1 : kP P) = 0 := card_nsmul_eq_zero'
        rw [hcard, nsmul_one] at hzero
        exact Ideal.Quotient.eq_zero_iff_mem.1 ((map_natCast _ q).trans hzero)
      exact hne k (GlobalTheory.ChainEquiv.eq_of_natCast_mem P' hq (D.host.g_prime k)
        (GlobalTheory.ChainEquiv.natCast_mem_of_isConjPl hc h1) (L.C.P.overP hk))
    · exact (hL.Q_pl t P h).2 P' h'

end Places

theorem liftsAt_and_seedFacts : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type)
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (F : Face D A), LiftsAt D A Ks F ∧ SeedFacts D A Ks F := by
  intro D G _ _ Pl0 T A Ks _ _ _ F
  refine ⟨fun R h => ⟨GlobalTheory.LevelRowsObj.liftsExist h.lev, fun i => GlobalTheory.GeoActRoad.levelLiftsExist_gridVertexSpaces h.lev i⟩, fun R h => ⟨?_, ?_⟩⟩
  · exact fun t => splitFacts h.lev t
  · classical
    intro t
    refine ⟨(GlobalTheory.ChainEquiv.places_sep R.toLevCh A.μ0 h.lev t).2, GlobalTheory.CentralShift.exists_idemSum _ fun P hP P' hP' => ?_⟩
    exact not_isConjPl_union h.lev t (Finset.mem_union.1 hP) (Finset.mem_union.1 hP')

end GlobalTheory.HeckeCharacterRestriction
end
end
