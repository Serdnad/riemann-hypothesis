module

public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.CoeffOneLNe
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.Bundle003
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementE
public import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
public import Formalism.LocalToGlobal.InertKernelTheory.K2OfAgreements
public import Formalism.SharpRestriction.GrowthBounds.LatticeMultiplicityLemmas.LatticeMultiplicityCheck.Retype
public import Formalism.LocalToGlobal.KernelLattices.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section

noncomputable section

namespace Formalism.L2.KerInert

open Formalism.MainNotions.GL3Theta Formalism.L2.G.Pend

def GenusOneModelExists : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ),
    Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc → Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], Nat.Coprime (Ideal.absNorm cc) p → 5 ≤ p → InertK D p →
    ∀ lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p],
      ∃ g : G1 p, g.lam = lam ∧ At D cc δ g ∧ ModelOverW g.lam g.abelian₂ g.C ∧ LTIso g

def GenusOneModelExistsLattice : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ),
    Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc → Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → InertK D p →
    ∀ lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p],
      ∃ (cc' : Ideal (NumberField.RingOfIntegers D.host.K)) (δ' : ℂ) (g : G1 p),
        Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc' ∧ Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc' δ' ∧
        Formalism.MainNotions.TaylorLogMetric.lamOf D cc' δ' = Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ ∧
        g.lam = lam ∧ At D cc' δ' g ∧ ModelOverW g.lam g.abelian₂ g.C ∧ LTIso g

end Formalism.L2.KerInert
end
end

section

noncomputable section

namespace Formalism.L2.KerInert

open MvPowerSeries Formalism.MainNotions.GL3Theta Formalism.L2.G.Pend

def BeWAt (D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (g : G1 p) : Prop :=
  CoefWf (g.be (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) ∧
    SimeqW (g.be (g.add (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 2) + g.be (Xv 1) (Xv 2)) ∧
    SimeqW (g.be (Xv 0) (g.add (Xv 1) (Xv 2)) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 1) + g.be (Xv 0) (Xv 2)) ∧
    ∀ α ∈ OKp D g.lam,
      SimeqW (g.be (g.mulBy α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
        (g.be (Xv 0) (g.mulBy α.2 (Xv 1)))

def BePropOfBeW : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ) (p : ℕ) [Fact p.Prime] (g : G1 p)
    (hLT : LTIso g), At D cc δ g → 5 ≤ p → InertK D p → ModelOverW g.lam g.abelian₂ g.C → BeWAt D g →
    Formalism.MainNotions.FormalGroupSystem.BeProp p (beLT hLT)

def Adm2cAt : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ) (p : ℕ) [Fact p.Prime] (g : G1 p)
    (hLT : LTIso g), At D cc δ g → 5 ≤ p → InertK D p → ModelOverW g.lam g.abelian₂ g.C → BeWAt D g →
    ∀ (X : Formalism.MainNotions.FormalGroupSystem.Sys p) (Y : Formalism.MainNotions.FormalGroupSystem.Pend X), Y.be = beLT hLT → Formalism.MainNotions.FormalGroupSystem.adm2c D X Y

end Formalism.L2.KerInert
end
end

section

noncomputable section

namespace Formalism.L2.KerInert.BeCob

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D
open Formalism.MainNotions.GL3Theta (G1 ModelOverW)
open Formalism.L2.G.Pend (k0ToC wToC LTIso beLT epOf BeRat)
open Formalism.InvariantFactorPaths.G7 (cob lgF IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.DworkPowerSeriesWeights (Integral)

def eLT {l : ℕ} [Fact l.Prime] {g : G1 l} (hLT : LTIso g) : ℂ_[l] := wToC l (epOf hLT : WW l)

def vLT {l : ℕ} [Fact l.Prime] {g : G1 l} (hLT : LTIso g) : PowerSeries ℂ_[l] :=
  PowerSeries.subst (PowerSeries.C (eLT hLT)⁻¹ * lgF ℂ_[l] l) g.ex

def psiLT {l : ℕ} [Fact l.Prime] {g : G1 l} (hLT : LTIso g) : PowerSeries ℂ_[l] :=
  PowerSeries.subst (vLT hLT) g.ph

def CobExact : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (g : G1 l) (hLT : LTIso g), g.Ok → BeRat g (eLT hLT) →
    ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
      MvPowerSeries.map (k0ToC l) (inParam l (beLT hLT)) =
        cob (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype F) (psiLT hLT)

def CobSimeq : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K),
    MvPowerSeries.constantCoeff F = 0 → Integral F →
    ∀ f f' : PowerSeries K, Formalism.InvariantFactorPaths.G7.Simeq (f : MvPowerSeries Unit K) f' →
      Formalism.InvariantFactorPaths.G7.Simeq (cob F f) (cob F f')

def PhTie : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (g : G1 l) (hLT : LTIso g), g.Ok → ∀ s2 : ℂ_[l],
    g.ph = Formalism.L2.Th1.B.phW g.W s2 →
    Formalism.InvariantFactorPaths.G7.Simeq (psiLT hLT : MvPowerSeries Unit ℂ_[l])
      (phFF l (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W) s2 (eLT hLT)⁻¹)

def ThetaTie : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (g : G1 l) (hLT : LTIso g), g.Ok →
    ∀ n, ‖PowerSeries.coeff n (thetaS l (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W) (eLT hLT)⁻¹)‖ ≤ 1

def BeCoef : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (g : G1 l), g.Ok → ModelOverW g.lam g.abelian₂ g.C → Formalism.MainNotions.GL3Theta.CoefWf g.ph →
    Formalism.MainNotions.GL3Theta.CoefWf (g.be (MvPowerSeries.X 0) (MvPowerSeries.X 1) : MvPowerSeries (Fin 2) ℂ_[l])

def ShortIso : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K], ‖(2 : K)‖ = 1 → ‖(3 : K)‖ = 1 →
    ∀ W : WeierstrassCurve K, Formalism.L2.Th1.A.IntModel W →
      Integral (PowerSeries.subst (Formalism.L2.Th1.A.logSer W)
        (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W))) : MvPowerSeries Unit K)

end Formalism.L2.KerInert.BeCob
end
end

section

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.SecondKernelInstances

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2

section Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX}
variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X)

def SecondKernelAtLevel (j : ℕ) : Prop :=
  ∃ cK : Y.Kc, cK ∈ Y.Oc ∧ cK⁻¹ ∈ Y.Oc ∧ cK ≠ 0 ∧
    ∀ F ∈ X.FQ j, ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
      MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (X.Kz j F c' L') =
        ∑ La ∈ Y.Rep j, (((X.stab j La : Y.Kc))⁻¹ * cK) • Y.ker j La (c', L') (F La.1 La.2)

variable {X Y}
variable (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)

def ClsBij (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j) (j : ℕ) : Prop :=
  Function.Bijective fun La : ↥(Y.Rep j) => cls j La.1.1 La.1.2

def FormsSharpAt (j : ℕ) : Prop :=
  ∀ x : ((ex.tw.fm u μ).lat j).V, ∃ Q, SharpQ t ex.tw u μ j x Q

def TieStabAt (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j) (j : ℕ) : Prop :=
  ∀ La ∈ Y.Rep j, Nat.card ((D.chTw u μ).stab j (cls j La.1 La.2)) = X.stab j La

def TieReadAt {σ : D.what₂.LL →+* X.G.Kf} (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) (ι : ℂ →+* Y.Kc)
    (Rd : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup →
      ((D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc) (j : ℕ) : Prop :=
  ∀ (y : ((ex.tw.fm u μ).lat (j + 1)).V) (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
    MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (cmp (j + 1) y c' L') = Rd j c' L' ((ex.tw.fm u μ).emb (j + 1) y)

def TieSerAt (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) (j : ℕ) : Prop :=
  ∀ La ∈ Y.Rep j, ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
    Y.ThF j La (c', L') = ((Y.eS j La * (Y.eT j (c', L'))⁻¹)⁻¹ : X.G.Kf) • Sr j La (c', L')

def KernelDifferenceAtLevel {σ : D.what₂.LL →+* X.G.Kf} (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j)
    (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) (ι : ℂ →+* Y.Kc)
    (Rd : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup →
      ((D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
    (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) (j : ℕ) (cK : Y.Kc) : Prop :=
  ∀ La ∈ Y.Rep j, ∀ (x : ((ex.tw.fm u μ).lat j).V) (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup),
    (X.Pj (j + 1)).IsLatTup L' →
      Rd j c' L' (entRec t ex.tw u μ j (cls j La.1 La.2) x) = cK • Y.DelF j (cmp j x La.1 La.2) (Sr j La (c', L'))

def TiesAt {σ : D.what₂.LL →+* X.G.Kf} (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j)
    (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) (ι : ℂ →+* Y.Kc)
    (Rd : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup →
      ((D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
    (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) (j : ℕ) : Prop :=
  FormsSharpAt t u μ j ∧ TieStabAt (Y := Y) u μ cls j ∧ TieReadAt u μ cmp ι Rd j ∧ TieSerAt Sr j ∧
    ∃ cK : Y.Kc, cK ∈ Y.Oc ∧ cK⁻¹ ∈ Y.Oc ∧ cK ≠ 0 ∧ KernelDifferenceAtLevel t u μ cls cmp ι Rd Sr j cK

end Gen

abbrev sysAt {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl} {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
    [Fact (D.what₂.places.resChar w).Prime] {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} (Ch : Chain Lv)
    (std : ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w h).P.n' v) (D.gat u w h).P.m Fl.t Fl.mm Fl.c (D.gat u w h).P.r
      (Fl.TT v) (Fl.a v) (Fl.b v) ((D.gat u w h).P.lam0 v) (Fl.w v))
    (vp : (D.gat u w h).O) (unif : Irreducible vp) (eO : ℕ)
    (eO_spec : Associated ((D.what₂.places.resChar w : ℕ) : (D.gat u w h).O) (vp ^ eO)) (dG : ℕ → ℕ)
    (dG_spec : ∀ j ≤ Fl.mm, ∀ (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
      padicValNat (D.what₂.places.resChar w) (Nat.card {γ : (Lv.lev j c).Γ // (Lv.lev j c).smul γ L = L}) ≤ dG j)
    (om : ∀ v, OmBasis (D.what₂.places.resChar w) ((D.gat u w h).P.n' v)) : Sys (D.what₂.places.resChar w) :=
  Sys.mk (D.gat u w h) Fl Lv Ch std vp unif eO eO_spec dG dG_spec om

def ClsBijInst : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om)) (j : ℕ), j ≤ D.R.m →
      ClsBij (Y := Y) u μ KA.cls j

def Adm3bInst : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv), TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch →
    ∀ (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _),
      adm3b D (sysAt Ch std vp unif eO eO_spec dG dG_spec om)

def SecondKernelSingleLevel : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om)) (ι : ℂ →+* Y.Kc) (Rd : _) (Sr : _) (j : ℕ),
    j < D.R.m → TiesAt t u μ KA.cls KA.cmp ι Rd Sr j → SecondKernelAtLevel _ Y j

def SecondKernelEntrywise : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om)) (ι : ℂ →+* Y.Kc) (Rd : _) (Sr : _),
    (∀ j, j + 1 < D.R.m → TiesAt t u μ KA.cls KA.cmp ι Rd Sr j) → ∀ j, j + 1 < D.R.m → SecondKernelAtLevel _ Y j

end Formalism.L2.KerInert.SecondKernelInstances
end
end

section

noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.KerInert

open Formalism.MainNotions Formalism.L2.Ker
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (thetaS)
open Formalism.L2.Th1.Top (IsLTNorm IsFrameH thetaH uniformGaussModelCondition)
open Formalism.L2.Th1.H (CmOK matH stdH stdLat pow4 imgLat relIdx StdData Th alphaQ kernel4 tens4)

def KapInert : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0),
    CmOK a₀ b₀ c₀ D.host.d → B.IsCm a₀ b₀ ha hd lam hlam →
    ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → jacobiSym (-(D.host.d : ℤ)) l = -1 → ∀ ι : ℂ ≃+* ℂ_[l], B.KappaAt l ι

def KappaFirstKernelHypothesis : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0),
    CmOK a₀ b₀ c₀ D.host.d → B.IsCm a₀ b₀ ha hd lam hlam →
    ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → jacobiSym (-(D.host.d : ℤ)) l = -1 → ∀ ι : ℂ ≃+* ℂ_[l],
    ∃ (g : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (e : ℂ),
      StdData B.L B.ω₀ (hOne B.L D.what₂.Tau) B.lamM (alphaQ B.cq (matH (hOne B.L D.what₂.Tau)))
        (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))) g ∧
      ¬ l ∣ relIdx (stdLat B.L (Fin 4 × D.what₂.Tau))
        (imgLat (g : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)) ∧
      ‖ι e‖ = 1 ∧
      B.thMM ∈ Th (matH (hOne B.L D.what₂.Tau)) (alphaQ B.cq (matH (hOne B.L D.what₂.Tau))) B.lamM ∧
      tens4 B.thMM = e • kernel4 B.L B.ω₀ B.lamM (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))) g

end Formalism.L2.KerInert
end
end

section

noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.KerInert

open Formalism.MainNotions Formalism.L2.Ker
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (thetaS)
open Formalism.L2.Th1.Top (IsLTNorm IsFrameH thetaH uniformGaussModelCondition)
open Formalism.L2.Th1.H (CmOK matH stdH stdLat pow4 imgLat relIdx StdData Th alphaQ kernel4 tens4)

def ThMMReBase : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), TaylorLogMetric.IsCurveIdeal D cc →
    ∃ (a₀ g : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (hl : (g : ℂ) * δ ≠ 0) (B' : Base D cc δ),
      CmOK a₀ b₀ c₀ D.host.d ∧ Ideal.absNorm cc = g ^ 2 * a₀ ∧ B'.IsCm a₀ b₀ ha hd ((g : ℂ) * δ) hl ∧
      B'.L.lattice = B.L.lattice ∧ B'.γ₀ = B.γ₀ ∧ B'.gC = B.gC ∧ B'.kappa = B.kappa ∧
      (B.ω₀ - B'.ω₀) / 2 ∈ B.L.lattice ∧ B'.IsThMM = B.IsThMM ∧ B'.thMM = B.thMM

end Formalism.L2.KerInert
end
end
