module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle753
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle684
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctionsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsPreserveThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle484
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle565
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle686
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle687
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.besselStep_lineComponent_eq_kappa_lattice_point : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F ρ h).Γ₀, ∃ w ∈ lineLat F ρ, ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).2 = (F.lnk ρ).κ _ w := by
  exact @GlobalTheory.LineComp.main
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.besselToFourierJacobi_mixedPieces_admissible : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), (pcBF W F ρ h).Is (F.dB ρ h) (F.dJ ρ h) (xZero (F.dJ ρ h)) W.ψ ∧ Splits (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (xZero (F.dJ ρ h)) (yBF F ρ h) W.ψ (latRow G (2 * ρ + 1)) := by
  first | exact @GlobalTheory.PcBF.pieces_bf | exact GlobalTheory.PcBF.pieces_bf | (intros; apply GlobalTheory.PcBF.pieces_bf <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.normalisedKernelExpansionSum_levelInvariant : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ → (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) → ∀ (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))),
    (∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (j : ℕ) (hj : 0 < j) (hjm : j < D.R.m) (k : FinPt G (.top j)),
      finG (G.V (.top j)) k ∈ S.levTop t Φ β j hjm →
      pairPts S τ (Function.update x j (x j * k)) y (Ψ (Function.update x j (x j * k) 0)) (F (y 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0))) ∧
    ((∀ (x : FinPt G (.top 0)) (k : FinPt G (.top 0)), finG (G.V (.top 0)) k ∈ G.Kplus → Ψ (x * k) = Ψ x) →
    ∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.top 0)),
      finG (G.V (.top 0)) k ∈ S.levTop t Φ β 0 (by have := D.R.two_le_m; omega) →
      pairPts S τ (Function.update x 0 (x 0 * k)) y (Ψ (x 0 * k)) (F (y 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0))) ∧
    (∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (i : ℕ) (hi : 0 < i) (him : i < D.R.m) (k : FinPt G (.grid i D.R.m)),
      finG (G.V (.grid i D.R.m)) k ∈ S.levRow t i him.le →
      pairPts S τ x (Function.update y i (y i * k)) (Ψ (x 0)) (F (Function.update y i (y i * k) 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0))) ∧
    (∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.grid D.R.m D.R.m)),
      x D.R.m = finEmb G.sp.topDec (y D.R.m) → finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl →
      pairPts S τ (Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k))) (Function.update y D.R.m (y D.R.m * k))
        (Ψ (Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k)) 0)) (F (Function.update y D.R.m (y D.R.m * k) 0)) =
      pairPts S τ x y (Ψ (x 0)) (F (y 0))) := by
  first | exact @GlobalTheory.ExpansionInvariance.levels_invariant | exact GlobalTheory.ExpansionInvariance.levels_invariant | (intros; apply GlobalTheory.ExpansionInvariance.levels_invariant <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (Wl : G.Weil) {t : T} {M : Vol G}

theorem Q_eq_colPer (hM : M.Is t) : ∀ (σ j : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (vN : VolN (besDecAt G j σ hj))
    (Φ : (chainFrom G Wl t hM σ j hj vN).Data), (chainFrom G Wl t hM σ j hj vN).IsTheta Φ →
    ∀ (F : Fn G (.grid D.R.m D.R.m)), IsContAut _ F → ∀ (φ : GA D (G.V (.top j)) → ℂ), IsContAut _ φ →
    ∀ (g : GA D (G.V (.grid D.R.m j))) (h : (chainFrom G Wl t hM σ j hj vN).Var),
      (chainFrom G Wl t hM σ j hj vN).Q Φ F φ g h = colPer Wl hM σ j hj vN Φ F φ g h
  | 0, j, hj, vN, Φ, hΦ, F, hF, φ, hφ, g, _ => LastSeeSawStep.main G Wl t hM j hj vN Φ.1 Φ.2 F φ hΦ.1 hΦ.2 hF hφ g
  | σ + 1, j, hj, vN, Φ, hΦ, F, hF, φ, hφ, g, h => by
    have ih := Q_eq_colPer hM σ (j + 1 + 1) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some Φ.2.2 hΦ.2.2 F hF
    let B := besAt G hM j (σ + 1) hj vN
    let J := jacAt G hM (j + 1) (σ + 1) (by omega)
    let B' := besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN (besDecAt G (j + 1 + 1) σ (by omega))).some
    let s₁ : StepBF Wl.ψ B J :=
      stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
    let s₂ : StepFB Wl.ψ J B' :=
      stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)) (besDecAt G (j + 1 + 1) σ (by omega))
    have t₁ : IsThetaFunO Wl.ψ B.V₀ J.W₀ (flatBF s₁ (s₁.om (g, h.1) Φ.1)) :=
      (GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) Wl.ψ).1 _ B J s₁ _ (s₁.weil.om_pres (g, h.1) _ hΦ.1)
    have t₂ : IsThetaFunO Wl.ψ J.W₀ B'.V₀ (flatFB s₂ (s₂.om (h.1, h.2.1) Φ.2.1)) :=
      (GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) Wl.ψ).2 _ J B' s₂ _ (s₂.weil.om_pres (h.1, h.2.1) _ hΦ.2.1)
    have hc := GlobalTheory.FinPl.ValDbl.contAut_hand0 s₁ s₂ (linkAt hM j σ hj vN (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some) hφ t₁ t₂
    have e := ih _ hc h.2.1 h.2.2
    refine e.trans ?_
    show colPer Wl hM σ (j + 1 + 1) _ _ Φ.2.2 F _ h.2.1 h.2.2 = colPer Wl hM σ (j + 1 + 1) _ _ Φ.2.2 F _ h.2.1 h.2.2
    congr 1
    exact dbl_hand_eq_biLift G Wl t hM σ j hj vN Φ.1 Φ.2.1 φ hΦ.1 hΦ.2.1 hφ g h.1 h.2.1

end GlobalTheory.RowChain

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (Wl : G.Weil) {t : T} {M : Vol G}

theorem iter_chain (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (hd : AllTheta G Wl t d) (F : Fn G (.grid D.R.m D.R.m))
    (hF : IsContAut _ F) (φ : GA D (G.V (.top 0)) → ℂ) (hφ : IsContAut _ φ)
    (hR : (chain G Wl t hM).Rapid (chainData G Wl t hM d) F) :
    (chain G Wl t hM).Iter ((chain G Wl t hM).Q (chainData G Wl t hM d) F φ 1)
      ((topLev G hM).per Wl.ψ φ ((chain G Wl t hM).down (chainData G Wl t hM d) F)) := by
  have h := (GlobalTheory.Unf.unfoldings_of_chain D).2.2.2.2.2.1 Wl.ψ _ _ _ (chain G Wl t hM) (chainData G Wl t hM d) F φ 1
    (chainData_isTheta G Wl t hM d hd) hF hφ hR
  have e : rTrans 1 ((chain G Wl t hM).down (chainData G Wl t hM d) F) = (chain G Wl t hM).down (chainData G Wl t hM d) F := by
    funext z; simp [rTrans]
  rwa [e] at h

theorem chain_Q_eq (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (hd : AllTheta G Wl t d) (F : Fn G (.grid D.R.m D.R.m))
    (hF : IsContAut _ F) (φ : GA D (G.V (.top 0)) → ℂ) (hφ : IsContAut _ φ) (h' : (chain G Wl t hM).Var) :
    (chain G Wl t hM).Q (chainData G Wl t hM d) F φ 1 h' =
      colPer Wl hM _ 0 top_idx (topVN hM) (chainData G Wl t hM d) F φ 1 h' :=
  Q_eq_colPer Wl hM _ 0 top_idx (topVN hM) _ (chainData_isTheta G Wl t hM d hd) F hF φ hφ 1 h'

theorem iter_colPer (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (hd : AllTheta G Wl t d) (F : Fn G (.grid D.R.m D.R.m))
    (hF : IsContAut _ F) (φ : GA D (G.V (.top 0)) → ℂ) (hφ : IsContAut _ φ)
    (hR : (chain G Wl t hM).Rapid (chainData G Wl t hM d) F) :
    (chain G Wl t hM).Iter (colPer Wl hM _ 0 top_idx (topVN hM) (chainData G Wl t hM d) F φ 1)
      ((topLev G hM).per Wl.ψ φ ((chain G Wl t hM).down (chainData G Wl t hM d) F)) := by
  have h := iter_chain Wl hM d hd F hF φ hφ hR
  have e : (chain G Wl t hM).Q (chainData G Wl t hM d) F φ 1 = colPer Wl hM _ 0 top_idx (topVN hM) (chainData G Wl t hM d) F φ 1 :=
    funext (chain_Q_eq Wl hM d hd F hF φ hφ)
  rwa [e] at h

end GlobalTheory.RowChain
end
end
