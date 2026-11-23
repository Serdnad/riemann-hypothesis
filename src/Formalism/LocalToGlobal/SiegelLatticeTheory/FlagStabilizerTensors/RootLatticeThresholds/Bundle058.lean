module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle056
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle051
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle045
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle101
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle038
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle027
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle028
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointPinNormSt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.MSTypP
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CfgTopFalseIff
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopsFinalS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle007
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle010
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SiegelMassRatioOfLI
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GrowthOfBasic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle137
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

theorem energy_compact_test_bound {D : D7} (T : Formalism.L2.SG.SpectralTiesReal.STies D) {θ : ℝ} (C : Choice T.X θ) (u u' : D.what₂.Word)
    (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie T.X e) (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2)
    (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (a b : ∀ j : Fin (nfE D), T.X.B.H (tauE T.X e j)) (ξ : ∀ j : Fin (nfE D), T.X.Vloc u (tauE T.X e j))
    (ξ' : ∀ j : Fin (nfE D), T.X.Vloc u' (tauE T.X e j)) (cc : Fin (nfE D) → ℂ)
    (i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (T.X.Vloc u (tauE T.X e j)) (T.X.Vloc u' (tauE T.X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf T.X C u u' e j).base.π
      (towersOf T.X C u u' e j).base.z (m0E T.X C u u' e j *ᵥ nuE T.X C u' e i0' j)) (A₀ : ℝ)
    (X0 : Fin (2 * D.R.rS + 2) → Fin T.X.B.I.n → T.X.B.I.E) (sd Cb Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Formalism.MainNotions.S.Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (i0b i0b' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf)
    (hpin : JointPin.PinCov (CarrierOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))))
    (hBuilt : Formalism.FourierDecayAlt.D.IsBuilt (_root_.Formalism.L2.SG.Pf.Carrier.sOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)) (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).T (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).fc (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).χ (nuE T.X C u' e i0') (m0E T.X C u u' e) (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).top A₀) :
    (∏ v, (Formalism.FourierDecayAlt.B.normSq ((ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).T v).base ((ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).fc v)).toReal /
        Formalism.FourierDecayAlt.D.GamLev (_root_.Formalism.L2.SG.Pf.Carrier.sOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).G.k (_root_.Formalism.L2.SG.Pf.Carrier.sOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).G.r (Formalism.FourierDecayAlt.D.kapG (_root_.Formalism.L2.SG.Pf.Carrier.sOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).g (Formalism.FourierDecayAlt.S6.rd D.host.E))
          (Formalism.FourierDecayAlt.D.deG (_root_.Formalism.L2.SG.Pf.Carrier.sOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).g (Formalism.FourierDecayAlt.S6.rd D.host.E)) 0) =
      (Formalism.L2.SG.SpectralTiesReal.massDataY T.X T.hb T.Y u u' X0 T.ψ sd Cb Th vR Q i0b i0b' νq).IntN := by
  have hFX : (CarrierOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))).FromX :=
    BaseOf.fromX T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd.χ (sgOf (Formalism.L2.SG.SpectralTiesReal.gOf D e) (plE D) ((D.mem u).A.T : ℝ) ((D.mem u').A.T : ℝ) de de' (l + 1))
      (nuE T.X C u' e i0') (m0E T.X C u u' e) (fun j => Formalism.FourierDecayAlt.Top.topOf (parE e u u' de de' j) (l + 1) (towersOf T.X C u u' e j) (nuE T.X C u' e i0' j)
        (m0E T.X C u u' e j) (Θ j) (TP j)) A₀ (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))
  have hg0 : 0 < (CarrierOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))).S.g := by
    show 0 < D.host.g 0 * D.host.g 1
    exact Nat.mul_pos (Formalism.L2.SG.Pf.CarrierSz.g_pos D).1 (Formalism.L2.SG.Pf.CarrierSz.g_pos D).2
  have hZ := zhatTr_carrierOf T.X u u' e he hv C CA de de' l (gridT e l) (grid1T e l) (towersOf T.X C u u' e)
    (Tz_towersOf_base_eq_T T.X C u u' e) (fcT T.X C e u u' a b ξ ξ' cc) cutStd.χ (sgOf (Formalism.L2.SG.SpectralTiesReal.gOf D e) (plE D) ((D.mem u).A.T : ℝ) ((D.mem u').A.T : ℝ) de de' (l + 1)) (nuE T.X C u' e i0') (m0E T.X C u u' e)
    (fun j => Formalism.FourierDecayAlt.Top.topOf (parE e u u' de de' j) (l + 1) (towersOf T.X C u u' e j) (nuE T.X C u' e i0' j)
        (m0E T.X C u u' e j) (Θ j) (TP j)) A₀ (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))
  have hPN := JointPin.placeNormG_of_pin (CarrierOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))) rfl hpin
    (JointPinNormSt.normBridge_of_zhat _ rfl hZ) hFX hBuilt hg0
  have hrd : Formalism.FourierDecayAlt.S6.rd D.host.E = D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE Formalism.FourierDecayAlt.S6.rd
    rw [Int.cast_abs, one_div]
  have hk1 : 1 ≤ (CarrierOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))).S.G.k := by
    show 1 ≤ D.R.k
    have := Formalism.MainNotions.BridgeLemma.five_le_k D
    omega
  exact EnergyNF.energy_norm_bound_third_form T.hb T.Y X0 T.ψ sd Cb Th vR Q i0b i0b' νq (CarrierOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))) rfl rfl
    (fun v => Tz_towersOf_base_eq_T T.X C u u' e _) rfl hrd hg0 hk1 (Formalism.L2.SG.WConst.card_places T.X) T.ψ_char T.ψ_std
    (Formalism.L2.SG.Pf.ProdConvCut2.prodConv_holds T u u') (Formalism.L2.S.Pv.MSTypP.lemmaMSStd_holds T.X u u' T.ψ) hPN

end Formalism.L2.SG.Pf.CarrierXAll
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf Formalism.L2.SG.LoopsFinal Formalism.FourierDecayAlt
  Formalism.L2.SG.ThmSOwn

namespace Formalism.L2.SG.LoopsTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SelQ

variable {𝒞 : FamClass} (sel : SSel 𝒞)

variable {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm)

end SelQ

section Closed

variable (C0 : ℝ) {𝒞 : FamClass} (sel : SSel 𝒞)

theorem cOut_take {eps : ℝ} (Fm : FamP eps) (CH : ℝ) : (Fm.cOut ++ Fm.cMid CH).take 16 = Fm.cOut := by
  unfold FamP.cOut; simp

theorem constant_list_cylinder {eps : ℝ} (Fm : FamP eps) (CH : ℝ) : (Fm.cOut ++ Fm.cMid CH).getD 6 0 = Fm.CYL := by
  unfold FamP.cOut; simp

theorem constant_list_trace {eps : ℝ} (Fm : FamP eps) (CH : ℝ) : (Fm.cOut ++ Fm.cMid CH).getD 13 0 = Fm.CTu := by
  unfold FamP.cOut; simp

end Closed

section Raised

variable (C0 : ℝ) {𝒞 : FamClass} (sel : SSel 𝒞)
  (yF : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → ℝ)

def YFOK : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : Fm.x1 < x) (h0 : (sel Fm hc).1 ≤ x), yF Fm hc ≤ x →
    ∀ i : Fm.Ix x, FinX ((sel Fm hc).2 x hx h0 i).Y ∧ Formalism.L2.SG.WuDecay.WuDecay ((sel Fm hc).2 x hx h0 i).X

def yR {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) : ℝ := max (sel Fm hc).1 (yF Fm hc)

theorem h0R {eps : ℝ} {Fm : FamP eps} {hc : 𝒞 Fm} {x : ℝ} (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) :
    (sel Fm hc).1 ≤ x :=
  ((le_max_left _ _).trans (le_max_right _ _)).trans hx.le

theorem hyR {eps : ℝ} {Fm : FamP eps} {hc : 𝒞 Fm} {x : ℝ} (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) :
    yF Fm hc ≤ x :=
  ((le_max_right _ _).trans (le_max_right _ _)).trans hx.le

def AtR (hyF : YFOK sel yF) {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) (x : ℝ) (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x)
    (i : Fm.Ix x) : TermTie (Fm.D x i) :=
  atOfW ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).Y
    (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1
    (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1)
    (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2

def CcR (hyF : YFOK sel yF) {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) (x : ℝ) (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x)
    (i : Fm.Ix x) : ConcAt0 (Fm.D x i) (AtR sel yF hyF Fm hc x hx i) :=
  ccOfW ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).Y
    (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1
    (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1)
    (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem loopRowS_of_raised (hyF : YFOK sel yF) (C1f : List ℝ → ℝ) (C₀f : (List ℝ → ℝ) → List ℝ → ℝ)
    (Yt : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word), LoopTie (Fm.D x i) (Fm.L x i) (AtR sel yF hyF Fm hc x hx i) u u' (C1f Fm.cOut))
    (hRowsF : ∀ aF : List ℝ → ℝ, Closed 𝒞 fun Fm CH => ∀ hc : 𝒞 Fm, ∀ C : ℝ, C₀f aF (Fm.cOut ++ Fm.cMid CH) ≤ C →
      OwnEv Fm fun C' Cl x i => ∀ (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (u u' : (Fm.D x i).what₂.Word),
        Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 (aF Fm.cOut) →
          Formalism.MainNotions.BridgeLemma.RowsND (AtR sel yF hyF Fm hc x hx i) (Yt Fm hc x hx i u u') C ∧
            Formalism.MainNotions.BridgeLemma.RowsDeg (AtR sel yF hyF Fm hc x hx i) (Yt Fm hc x hx i u u') C ∧
            Formalism.MainNotions.BridgeLemma.RowsOne (AtR sel yF hyF Fm hc x hx i) (Yt Fm hc x hx i u u') C)
    (hForm : Closed 𝒞 fun Fm _ => OwnEv Fm fun C' Cl x i =>
      Hyp0 (Fm.D x i) (Fm.L x i) C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) :
    LoopRowS C0 𝒞 sel := by
  intro aF
  choose f g hfg using fun p : ℝ × ℝ × ℝ × ℝ =>
    loop_evaluation_threshold_zero Formalism.FourierDecayAlt.P.loop_kernels Formalism.FourierDecayAlt.P.subfamilyAlt Formalism.HermitianLattices.Ext.L3.siegelMassRatio
      (p.1 + 1) (1 / 4) 3 (1 / 2) p.2.1 C0 p.2.2.1 p.2.2.2
  let par : List ℝ → ℝ × ℝ × ℝ × ℝ := fun l => (l.getD 6 0, l.getD 13 0, aF (l.take 16), C₀f aF l)
  obtain ⟨e1, he1, H1⟩ := hRowsF aF
  obtain ⟨e2, he2, H2⟩ := hForm
  refine ⟨min e1 e2, lt_min he1 he2, fun eps he hle => ?_⟩
  obtain ⟨K1, hK1⟩ := H1 eps he (hle.trans (min_le_left _ _))
  obtain ⟨K2, hK2⟩ := H2 eps he (hle.trans (min_le_right _ _))
  let K4 : TransportedAlt := ⟨0, fun _ => 0, fun _ => 0, fun l => max (f (par l)) (g (par l))⟩
  refine ⟨(K1.sup K2).sup K4, fun Fm CH hc hL => ?_⟩
  obtain ⟨hL12, hL4⟩ := (Fm.large_sup _ _ CH).1 hL
  obtain ⟨hL1, hL2⟩ := (Fm.large_sup _ _ CH).1 hL12
  intro hc'
  have epar : par (Fm.cOut ++ Fm.cMid CH) = (Fm.CYL, Fm.CTu, aF Fm.cOut, C₀f aF (Fm.cOut ++ Fm.cMid CH)) := by
    simp only [par, constant_list_cylinder, constant_list_trace, cOut_take]
  have hthr : ∀ c ∈ Fm.cLast, max (f (Fm.CYL, Fm.CTu, aF Fm.cOut, C₀f aF (Fm.cOut ++ Fm.cMid CH)))
      (g (Fm.CYL, Fm.CTu, aF Fm.cOut, C₀f aF (Fm.cOut ++ Fm.cMid CH))) ≤ c := by
    intro c hc0
    have := hL4.2.2.2 c hc0
    simpa only [K4, epar] using this
  have hC' : f (Fm.CYL, Fm.CTu, aF Fm.cOut, C₀f aF (Fm.cOut ++ Fm.cMid CH)) ≤ sC' Fm :=
    (le_max_left _ _).trans (hthr _ (by unfold FamP.cLast sC'; simp))
  have hCl : g (Fm.CYL, Fm.CTu, aF Fm.cOut, C₀f aF (Fm.cOut ++ Fm.cMid CH)) ≤ sCl Fm := by
    have h := fun c hc => (le_max_right _ _).trans (hthr c hc)
    unfold sCl
    refine le_min (h _ (by unfold FamP.cLast; simp)) (le_min (h _ (by unfold FamP.cLast; simp))
      (le_min (h _ (by unfold FamP.cLast; simp)) (le_min (h _ (by unfold FamP.cLast; simp))
        (le_min (h _ (by unfold FamP.cLast; simp)) (h _ (by unfold FamP.cLast; simp))))))
  have hE := hfg (Fm.CYL, Fm.CTu, aF Fm.cOut, C₀f aF (Fm.cOut ++ Fm.cMid CH)) (Fm.raise (yR sel yF Fm hc')) (C1f Fm.cOut)
    (AtR sel yF hyF Fm hc') (Yt Fm hc') (CcR sel yF hyF Fm hc') (hK1 Fm CH hc hL1 hc') (hK2 Fm CH hc hL2)
  obtain ⟨x0, H⟩ := hE
  refine ⟨max x0 (yR sel yF Fm hc' + 1), fun x hx0 i => ?_⟩
  intro hx h0 u u' hH hCT hA
  have hx' : (Fm.raise (yR sel yF Fm hc')).x1 < x := by
    show max Fm.x1 (yR sel yF Fm hc') < x
    refine max_lt hx ?_
    have := (le_max_right _ _).trans hx0
    linarith
  exact H x ((le_max_left _ _).trans hx0) i hC' hCl hx' u u' hH hCT hA

theorem constant_list_gamma {eps : ℝ} (Fm : FamP eps) (CH : ℝ) : (Fm.cOut ++ Fm.cMid CH).getD 17 0 = Fm.CGam := by
  unfold FamP.cOut FamP.cMid; simp


end Raised

end Formalism.L2.SG.LoopsTies
end
end
