module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle994
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Definitions.Foundations.EisValueAtIffEisPoleLE
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SiegelWeilAnisotropicUnitary
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ParBoundW (D : D7) : Prop := ForStage D fun c _ s => ∀ (u : s.CC c) B, IsPar u B →
  GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B s.V.rank ((s.V.rank : ℝ) / 2)

def ChainLW (D : D7) : Prop := ∀ c : Com D, c.Is → ∀ B : GlobalTheory.LFun.Fam D.host.E,
  GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B D.R.r ((D.R.r : ℝ) / 2) →
  ∀ k < D.R.m, LNe c (c.chT (k + 1)) (chainPar c B k)

def Com.eps {D : D7} (c : Com D) (k : ℕ) : (AE D)ˣ →* Circle := if Odd k then c.η⁻¹ else 1

def ChainUp (D : D7) : Prop :=
  GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → ∀ c : Com D, c.Is → ∀ s₀ : PiLocalization₂ D, s₀.Is c 0 →
    ∀ k ≤ D.R.m, ∀ (s : PiLocalization₂ D) (Θ : s.CC c →ₗ[ℂ] s₀.CC c), Reach c s₀ k s Θ → s.Is c k ∧
      ∀ ipD₀ ip₀ ipD ip, IsMet c s₀ ipD₀ ip₀ → IsMet c s ipD ip → ∀ (u : s₀.CC c) B, IsPar u B →
        ∃ x : s.CC c, (∀ y, ip y x = ip₀ (Θ y) u) ∧ IsPar x (chainPar c B k)

end GlobalTheory.ChainOnto

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section OfTower

variable (W : GlobalTheory.Core.Rk.Tower D)

def comOf : Com D := ⟨W.θ, W.ψ, W.toLevCh.mu (), W.eta, W.Pg, W.triv, W.chi⟩

def stageY (j : ℕ) : PiLocalization₂ D :=
  ⟨Yc D j, parB (Ptw D) (min j D.R.m), W.MY j, W.ΛY j, W.βY j, W.datYt () j W.triv, W.νY j, W.fdY j⟩

def stageX : PiLocalization₂ D := ⟨D.sp.X', parB (Ptw D) D.R.m, W.MX, W.ΛX, W.βX, W.datXt (), W.νX, W.fdX⟩

def stepY (k : ℕ) : Step (comOf W) (stageY W k) (stageY W (k + 1)) := ⟨W.ωY k, W.vY k, W.ItY k, W.ioY k⟩

def stepX : Step (comOf W) (stageY W (D.R.m - 1)) (stageX W) := ⟨W.ωX, W.vX, W.ItX, W.ioX⟩

end OfTower

def PiLocalization₂.InFlag (s : PiLocalization₂ D) (κ : GA D s.V) : Prop :=
  κ ∈ GfC s.V ∧ Lev.finE s.V κ ∈ Formalism.L2.DIV.parLev D.sp.cm s.V.gram s.β s.L

def SameBlock (s s' : PiLocalization₂ D) (κ : GA D s.V) (κ' : GA D s'.V) : Prop :=
  HEq (Formalism.L2.DIV.rTup s.β s.L (Lev.finE s.V κ)) (Formalism.L2.DIV.rTup s'.β s'.L (Lev.finE s'.V κ'))

end GlobalTheory.ChainOnto

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.FinZeta (Gv embV VacFin)
open GlobalTheory.AdelicU (frameLat)

namespace GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def TransferOn (D : D7) (C : HeightOneSpectrum (𝓞 D.host.F) → Prop) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ t : ℕ, T.rank = S.rank + t →
  ∀ v, C v → (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χS w' ∧ GlobalTheory.LFun.UnrAt χT w') →
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (U : Submodule ℂ (WO S T → ℂ))
    (hU : ∀ a a', ∀ u ∈ U, om (embV S v a, embV T v a') u ∈ U) (f : U), VacFin ψ S T v f →
  ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Gv S v) X) (x : X) (B : Multiset ℂˣ),
    GlobalTheory.LFun.IsParamVec D.sp.cm.sig S.gram (frameLat S) h ρ x B →
  ∀ (X' : Type) [AddCommGroup X'] [Module ℂ X'] (ρ' : Representation ℂ (Gv T v) X') (b : U →ₗ[ℂ] X →ₗ[ℂ] X'),
    (∀ a a' (u : U) y, b ⟨om (embV S v a, embV T v a') u, hU a a' u u.2⟩ (ρ a y) = ρ' a' (b u y)) → b f x ≠ 0 →
    GlobalTheory.LFun.IsParamVec D.sp.cm.sig T.gram (frameLat T) h ρ' (b f x) (stepPar χS χT t (fun _ => B) w)

def CosetSym {G : Type} [Group G] (K : Subgroup G) : Prop :=
  ∀ g : G, Nat.card {c : G ⧸ K // ∃ k ∈ K, c = ((k * g : G) : G ⧸ K)} = Nat.card {c : G ⧸ K // ∃ k ∈ K, c = ((k * g⁻¹ : G) : G ⧸ K)}

end GlobalTheory.ChainOnto

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def comL (L : LevCh D Unit) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (P : LevelP L.Pg D.R.r ℂ) : Com D :=
  ⟨θ, ψ, L.mu (), L.eta, L.Pg, P, L.chi⟩

theorem mem_S {L : LevCh D Unit} (hL : L.Is ()) (θ ψ P) (k : Fin 2) (Q : Pl D.host.E)
    (hk : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal) : Q.under (𝓞 D.host.F) ∈ (comL L θ ψ P).S := by
  classical
  unfold Com.S
  rw [Finset.mem_image]
  rcases GlobalTheory.ConjOverQuad.div_or_conj_div D L.C.P k Q hk with h1 | ⟨Q', h1, hc⟩
  · exact ⟨Q, (hL.Pg Q).2 ⟨k, h1⟩, rfl⟩
  · refine ⟨Q', (hL.Pg Q').2 ⟨k, h1⟩, ?_⟩
    ext x
    show algebraMap _ _ x ∈ Q'.asIdeal ↔ algebraMap _ _ x ∈ Q.asIdeal
    rw [hc, Formalism.L2.Col.mem_conjIdeal]
    have : Formalism.L2.Col.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) = algebraMap _ _ x := by
      apply RingOfIntegers.ext
      exact (D.sp.cm.fixed _).2 ⟨x, rfl⟩
    rw [this]

end GlobalTheory.ChainOnto.Model

end
end

section

noncomputable section

namespace GlobalTheory.Core.Rk.Exh

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}


open Classical in
def under (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) : Finset (FinPl D) := Z.image fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)

def prinDat (A : HSp D) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) : Formalism.L2.DIV.LevDat D.host.E ℂ A.rank :=
  Formalism.IndefR.Lev.datW A.rank Z (Formalism.L2.DIV.LevelP.triv _ _ _) Formalism.IndefR.Lev.Frm.B

def prin (A : HSp D) (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) : Subgroup (GA D A) :=
  Formalism.IndefR.Lev.levG A β (prinDat A Z)

def prinInf (A : HSp D) (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) : Set (GA D A) :=
  {g | Formalism.IndefR.Lev.finE A g ∈ Formalism.L2.DIV.lev D.sp.cm A.gram β (prinDat A Z)}

def NoLift (ψ : AddChar (AF D.host.F) ℂ) {A W : HSp D} (om : WRep A W) (m : Measure (GA D A)) (u : GA D A → ℂ) : Prop :=
  ∀ f, IsThetaFunO ψ A W f → ∀ h, up om m f u h = 0

def Kills (ψ : AddChar (AF D.host.F) ℂ) {A W : HSp D} (χ : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) W) (m : Measure (GA D A))
    (u : GA D A → ℂ) : Prop :=
  ∀ φ, IsThetaFunO ψ (dblSp A) W φ → ∀ h,
    Eis.dblInt A χ⁻¹ m (fun g => thetaKO omh g h φ) (fun g => conj (u g)) (fun g => conj (u g)) = 0

structure Defin (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) : Prop where
  inf : IsInfFam θ
  sig : HSpace.SigOK A
  pos : HSpace.IsPosDef A
  cart : IsCartanFrame A cA
  one : ∀ τ, IsCartanInv (gramAt D A τ) 1
  cA_eq : ∀ τ, cA τ * (1 : Matrix (Fin A.rank) (Fin A.rank) ℂ) = Formalism.UG.Jpq (A.sig (tauE D τ)).1 (A.sig (tauE D τ)).2 * cA τ
  maj : IsMaj A a
  maj_eq : ∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D A τ * 1) * compAt θ τ a.1 = 1

structure Places (A : HSp D) (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) : Prop where
  frame : Formalism.L2.DIV.IsFrame β (frameLat A)
  idem : ∃ e : AE D, IsIdemSum e Z
  two : ∀ v : FinPl D, (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v

structure Form (θ : InfFam D) (A : HSp D) (cA : CptF A) (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D))
    (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) (χW : (AE D)ˣ →* Circle) (r t : ℕ) (u : GA D A → ℂ) (par : LFun.Fam D.host.E) : Prop where
  mem : u ∈ A0 θ A cA
  fix : ∀ κ ∈ prin A β Z, ∀ g, u (g * κ) = u g
  param : LFun.IsParamFun D.sp.cm.sig A.gram (frameLat A) (under Z : Set (FinPl D)) u par
  unr : LFun.UnrOff χW (under Z : Set (FinPl D))
  str : ∃ c, GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.Hyp (under Z : Set (FinPl D)) r t c par (LFun.val (F := D.host.F) χW) (LFun.val (F := D.host.F) χW)

structure Occ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {A W : HSp D} (sW : RealMat W) (om : WRep A W) (m : Measure (GA D A))
    (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) (u : GA D A → ℂ) (Φ : WO A W → ℂ) : Prop where
  cart : ∀ τ, IsCartanInv (gramAt D W τ) (sW τ)
  fock : IsFockVec ψ θ A W (fun _ => 1) sW Φ
  sph : IsSphOff ψ A W (frameLat A) (frameLat W) (under Z) Φ
  fix : ∀ κ ∈ prin A β Z, om (κ, 1) Φ = Φ
  real : ∀ ν 𝓕, IsCovolOne (ratL W A) ν 𝓕 → ∀ mR : Measure (GinfC A), mR.IsHaarMeasure →
    ∫ b : GinfC A, wcoef om ν 𝓕 Φ Φ b * rcoef m u u b ∂mR ≠ 0

def DownNe (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A W : HSp D) (t : ℕ) (χA χW : (AE D)ˣ →* Circle) (om : WRep A W)
    (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E))
    (m : Measure (GA D A)) (u : GA D A → ℂ) (par : LFun.Fam D.host.E) (sW : RealMat W) (Φ : WO A W → ℂ),
    Defin θ A cA a → HSpace.SigOK W → 0 < W.rank → A.rank = W.rank + t → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) →
    IsWeilDatumO ψ A W χA χW om → Places A β Z → m.IsHaarMeasure → Form θ A cA β Z χW W.rank t u par →
    Occ ψ θ sW om m β Z u Φ → ¬ NoLift ψ om m u

end GlobalTheory.Core.Rk.Exh

end
end

section

noncomputable section

namespace GlobalTheory.Core.Rk.IP

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SiegelWeilFock (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), 1 ≤ A.rank → A.rank < B.rank →
    (wittIndex B = 0 ∨ A.rank + wittIndex B < B.rank) →
  ∀ (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh →
  ∀ a : GL (Fin A.rank) (AE D), IsMaj A a →
  ∀ (θ : InfFam D) (sS : RealMat (dblSp A)) (sB : RealMat B), IsInfFam θ →
    (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) →
    (∀ k ∈ Khat A a, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * sS τ =
      sS τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k)) →
  ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 →
  ∀ mH : Measure (GA D B), mH.IsHaarMeasure →
  ∀ φ : WO (dblSp A) B → ℂ, IsFockVec ψ θ (dblSp A) B sS sB φ →
    (∀ g, Integrable (AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO omh g h φ) (autMeasure B mH)) ∧
    Eis.EisValueAt A (flat A a (swSec A B omh ν 𝓕 φ) (sZero A B)) (sZero A B) (ThetaMean.thetaMean omh mH φ)

end GlobalTheory.Core.Rk.IP

end
end
