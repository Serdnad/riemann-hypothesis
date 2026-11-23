module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle742
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VanishingDescendsBesselToFourierJacobi
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VanishingDescendsFourierJacobiToBessel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle310
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle375
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairVecSumEqOfProdEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle743
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle619
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle328
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProdExpansionFunctionsRowVertexInvariant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle548
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle739
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle661
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle667
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle660
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.standard_frames_successive_levels : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, GoodAt (F.dJ (σ + 1) h) (F.dB σ h') (xFB F σ h') W.ψ (G.Λ (.grid (2 * σ + 3) 0)) (G.Λ (.core (2 * σ + 3))) (G.Λ (.grid (2 * σ + 2) 0)) (lat0 F σ h') v ∧ StdAt (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') (G.Λ (.grid (2 * σ + 3) 0)) (G.Λ (.grid (2 * σ + 2) 0)) v := by
  first | exact @GlobalTheory.AscFin.GoodFB.goodAt_stdAt_fb | exact GlobalTheory.AscFin.GoodFB.goodAt_stdAt_fb | (intros; apply GlobalTheory.AscFin.GoodFB.goodAt_stdAt_fb <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integrand_supported_on_cells_largeDepth : Big fun ch => ∀ s, FlatAt ch s → OffAt ch → InvAt ch → TensAt ch → BasicAt ch → SuppOn ch s := by
  first | exact @GlobalTheory.RowVal.big_suppOn_of_flat | exact GlobalTheory.RowVal.big_suppOn_of_flat | (intros; apply GlobalTheory.RowVal.big_suppOn_of_flat <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.flat_dictionary_base_vacua_large_depth : Big fun ch => ∃ s, LocAt ch s := by
  first | exact @GlobalTheory.RowVal.exists_locAt_big | exact GlobalTheory.RowVal.exists_locAt_big | (intros; apply GlobalTheory.RowVal.exists_locAt_big <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.vanishing_descends_bessel_to_fourierJacobi : ∀ D : D7, VanBF D := by
  first | exact @GlobalTheory.Asc.vanBF | exact GlobalTheory.Asc.vanBF | (intros; apply GlobalTheory.Asc.vanBF <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.vanishing_descends_fourierJacobi_to_bessel : ∀ D : D7, VanFB D := by
  first | exact @GlobalTheory.Asc.VanJac.vanFB | exact GlobalTheory.Asc.VanJac.vanFB | (intros; apply GlobalTheory.Asc.VanJac.vanFB <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.expansion_pairing_invariant_last_vertex_level : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) →
    (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) →
    t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))),
    ∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.grid D.R.m D.R.m)),
      x D.R.m = finEmb G.sp.topDec (y D.R.m) → finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl →
      pairPts S τ (Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k))) (Function.update y D.R.m (y D.R.m * k))
        (Ψ (Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k)) 0)) (F (Function.update y D.R.m (y D.R.m * k) 0)) =
      pairPts S τ x y (Ψ (x 0)) (F (y 0)) := by
  first | exact @GlobalTheory.LastVertexInv.pairPts_last_invariant | exact GlobalTheory.LastVertexInv.pairPts_last_invariant | (intros; apply GlobalTheory.LastVertexInv.pairPts_last_invariant <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopZeroInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem pairVec_move (S : GridChoice W U) {t : T} (fs : Vecs G t) (hf : IsThetaFunO W.ψ _ _ (fs first))
    (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.top 0)) :
    pairVec S (Function.update x 0 (x 0 * k)) y fs =
      pairVec S x y (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs) := by
  have hj : ∀ j, (if h : j < D.R.m then kkVec S (.top t j) (fs (.inl ⟨j, h⟩)) (Function.update x 0 (x 0 * k) j)
          (Function.update x 0 (x 0 * k) (j + 1)) else 0) =
        (if h : j < D.R.m then kkVec S (.top t j)
          (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) := by
    intro j
    by_cases h : j < D.R.m
    · rw [dite_eq_left h, dite_eq_left h]
      rcases j with _ | j
      · have e1 : Function.update x 0 (x 0 * k) 0 = x 0 * k := Function.update_self _ _ _
        have e2 : Function.update x 0 (x 0 * k) (0 + 1) = x (0 + 1) := Function.update_of_ne (by omega) _ _
        have e3 : moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs (.inl ⟨0, h⟩) =
            W.om (.top t 0) (G.toPair (.top t 0) ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)).1 1) (fs first) :=
          Function.update_self _ _ _
        rw [e1, e2, e3]
        unfold kkVec
        have e4 : x 0 * k * S.N.u (Pair.small (.top t 0)) =
            (x 0 * S.N.u (.top 0)) * ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) := by group
        rw [e4, GlobalTheory.KerTrans.fockComp_mul_fin W _ (p := .top t 0) (show (Pair.top t 0 : Pair T).InRange D.R.m from
          show 1 ≤ D.R.m by have := D.R.two_le_m; omega) (fs (.inl ⟨0, h⟩)) hf]
        rfl
      · have e1 : Function.update x 0 (x 0 * k) (j + 1) = x (j + 1) := Function.update_of_ne (by omega) _ _
        have e2 : Function.update x 0 (x 0 * k) (j + 1 + 1) = x (j + 1 + 1) := Function.update_of_ne (by omega) _ _
        have e3 : moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs (.inl ⟨j + 1, h⟩) = fs (.inl ⟨j + 1, h⟩) :=
          Function.update_of_ne (by simp [first]) _ _
        rw [e1, e2, e3]
    · rw [dite_eq_right h, dite_eq_right h]
  have hcol : colV S fs (Function.update x 0 (x 0 * k)) =
      colV S (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs) x := by
    have hfam : (fun j => if h : j < D.R.m then kkVec S (.top t j) (fs (.inl ⟨j, h⟩)) (Function.update x 0 (x 0 * k) j)
          (Function.update x 0 (x 0 * k) (j + 1)) else 0) =
        (fun j => if h : j < D.R.m then kkVec S (.top t j)
          (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) :=
      funext hj
    unfold colV
    rw [hfam]
  have hri : ∀ i, (if h : i < D.R.m then kkVec S (.chi i D.R.m) (fs (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) =
      (if h : i < D.R.m then kkVec S (.chi i D.R.m)
        (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) := by
    intro i
    by_cases h : i < D.R.m
    · rw [dite_eq_left h, dite_eq_left h]
      have e3 : moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs (.inr ⟨i, h⟩) = fs (.inr ⟨i, h⟩) :=
        Function.update_of_ne (by simp [first]) _ _
      rw [e3]
    · rw [dite_eq_right h, dite_eq_right h]
  have hrow : rowV S fs y = rowV S (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs) y := by
    have hfam : (fun i => if h : i < D.R.m then kkVec S (.chi i D.R.m) (fs (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) =
      (fun i => if h : i < D.R.m then kkVec S (.chi i D.R.m)
        (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) := funext hri
    unfold rowV
    rw [hfam]
  unfold pairVec
  rw [hcol, hrow]

theorem pairPts_update_top_zero : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))),
    (∀ (x : FinPt G (.top 0)) (k : FinPt G (.top 0)), finG (G.V (.top 0)) k ∈ G.Kplus → Ψ (x * k) = Ψ x) →
    ∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.top 0)),
      finG (G.V (.top 0)) k ∈ S.levTop t Φ β 0 (by have := D.R.two_le_m; omega) →
      pairPts S τ (Function.update x 0 (x 0 * k)) y (Ψ (x 0 * k)) (F (y 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0)) := by
  intro D T L sc G W U S t Φ β τ μ₀ hL hq hc ht hβ hτ hv Ψ F hΨ x y k hk
  have hk' : finG (G.V (.top 0)) k ∈ G.Kplus := hk
  rw [hΨ _ _ hk', pairPts_eq, pairPts_eq]
  have hth : ∀ d ∈ τ.support, ∀ l, IsThetaFunO W.ψ _ _ (vecsOf S d l) := fun d hd l => by
    rcases l with j | i
    · exact GlobalTheory.TopZeroInv.vec_isThetaFunO S (p := .top t j) (show DefPair D.R.m (Pair.top t (j : ℕ)) from j.2) _ ((hv d hd).1 j)
    · exact GlobalTheory.TopZeroInv.vec_isThetaFunO S (p := .chi i D.R.m) (show DefPair D.R.m (Pair.chi (i : ℕ) D.R.m : Pair T) from ⟨i.2, rfl⟩) _ ((hv d hd).2 i)
  have hp0 : (Pair.top t 0 : Pair T).InRange D.R.m := show 1 ≤ D.R.m by have := D.R.two_le_m; omega
  have hmv : ∀ d ∈ τ.support, ∀ l,
      IsThetaFunO W.ψ _ _ (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) (vecsOf S d) l) := by
    intro d hd l
    by_cases hl : l = first
    · subst hl
      have e : moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) (vecsOf S d) first =
          W.om (.top t 0) (G.toPair (.top t 0) ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)).1 1) (vecsOf S d first) :=
        Function.update_self _ _ _
      rw [e]
      exact (W.om_is _ hp0).om_pres _ _ (hth d hd first)
    · have e : moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) (vecsOf S d) l = vecsOf S d l :=
        Function.update_of_ne hl _ _
      rw [e]
      exact hth d hd l
  calc (τ.sum fun d a => a * pairVec S (Function.update x 0 (x 0 * k)) y (vecsOf S d) (Ψ (x 0)) (F (y 0)))
      = τ.sum fun d a => a * pairVec S x y (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) (vecsOf S d))
          (Ψ (x 0)) (F (y 0)) :=
        Finset.sum_congr rfl fun d hd => by dsimp only; rw [pairVec_move S _ (hth d hd first)]
    _ = τ.sum fun d a => a * pairVec S x y (vecsOf S d) (Ψ (x 0)) (F (y 0)) :=
        GlobalTheory.TopZeroInv.pairVec_sum_eq_of_prod_eq S τ _ _ x y _ _ hmv hth (GlobalTheory.T.unfoldingExpansion_productFunction_fixed_by_Kplus S ht hL hq hc ht hβ hτ hv k hk')

end GlobalTheory.TopZeroInv
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.sum_prod_expansion_functions_rowVertex_invariant : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ → (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)), finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ c₁ c₂ : ℂ, W.om (.chi j D.R.m) (G.toPair (.chi j D.R.m) 1 (moved S j k)) (S.Z.vac (.chi j D.R.m)) = c₁ • S.Z.vac (.chi j D.R.m) → W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (S.Z.vac (.chi (j + 1) D.R.m)) = c₂ • S.Z.vac (.chi (j + 1) D.R.m) → ∀ z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)), (τ.sum fun d c => c * ∏ a, (scaleAt j hj c₁ c₂ a • movFn S j hj k (fnOf d) a) (z a)) = τ.sum fun d c => c * ∏ a, fnOf d a (z a) := by
  first | exact @GlobalTheory.RowVertexInv.sum_prod_scale_movFn_eq | exact GlobalTheory.RowVertexInv.sum_prod_scale_movFn_eq | (intros; apply GlobalTheory.RowVertexInv.sum_prod_scale_movFn_eq <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SquareDict

theorem dict : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m)
    (A : Fr (G.V (.grid (↑i + 1) (↑j + 1)))) (A₁ : Fr (G.V (.grid ↑i ↑j))) (AV : Fr (G.V (.grid ↑i (↑j + 1)))) (AV₁ : Fr (G.V (.grid (↑i + 1) ↑j))),
    GlobalTheory.SquareDict.IsGridFr W _ A → GlobalTheory.SquareDict.IsGridFr W _ A₁ → GlobalTheory.SquareDict.IsGridFr W _ AV →
    GlobalTheory.SquareDict.IsGridFr W _ AV₁ →
    (SquareStanding G t → ∀ M : Vol G, M.Is t →
      GlobalTheory.SquareComm.IsTriple (G.V (.grid (↑i + 1) (↑j + 1))) (G.V (.grid ↑i ↑j)) (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j))) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j)) ∧
    ∀ (ωA : GlobalTheory.Grid.WRep (G.V (.grid (↑i + 1) (↑j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j)))) (ωB : GlobalTheory.Grid.WRep (G.V (.grid ↑i ↑j)) (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j)))),
    GlobalTheory.Grid.IsWeil W.ψ true _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) ωA →
    GlobalTheory.Grid.IsWeil W.ψ false _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) ωB →
    ∃ κ : GA D (G.V (.grid ↑i (↑j + 1))) × GA D (G.V (.grid (↑i + 1) ↑j)) → ℂ,
    ∀ (B : Frames G) (ρ : RealMatch W) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)), IsMatched B t ρ i j Θ Θ' →
      GlobalTheory.SquareDict.datumA W Θ ∈ GlobalTheory.SquareComm.algF W.ψ W.θ true A (GlobalTheory.SquareComm.frSum AV AV₁) ∧
      GlobalTheory.SquareDict.datumB W Θ' ∈ GlobalTheory.SquareComm.algF W.ψ W.θ false A₁ (GlobalTheory.SquareComm.frSum AV AV₁) ∧
      (∀ g g₁ u, kerBig W Θ g g₁ u = κ (g, g₁) * thetaKO ωA u (GlobalTheory.SquareComm.blk _ _ (g, g₁)) (GlobalTheory.SquareDict.datumA W Θ)) ∧
      (∀ (z : GA D (G.V (.grid ↑i ↑j)) →₀ ℂ) g g₁ u, translates z (kerSmall W Θ' g g₁) u =
        κ (g, g₁) * thetaKO ωB u (GlobalTheory.SquareComm.blk _ _ (g, g₁)) (GlobalTheory.SquareDict.zact ωB z (GlobalTheory.SquareDict.datumB W Θ'))) ∧
      (∀ (M : Vol G) g g₁, ∫ u in M.fd _, kerBig W Θ g g₁ u ∂M.ν _ =
        κ (g, g₁) * GlobalTheory.SquareComm.thetaInt ωA (M.ν _) (M.fd _) (GlobalTheory.SquareDict.datumA W Θ) (GlobalTheory.SquareComm.blk _ _ (g, g₁))) ∧
      ∀ (M : Vol G) (z : GA D (G.V (.grid ↑i ↑j)) →₀ ℂ) g g₁, ∫ u in M.fd _, translates z (kerSmall W Θ' g g₁) u ∂M.ν _ =
        κ (g, g₁) * GlobalTheory.SquareComm.thetaInt ωB (M.ν _) (M.fd _) (GlobalTheory.SquareDict.zact ωB z (GlobalTheory.SquareDict.datumB W Θ'))
          (GlobalTheory.SquareComm.blk _ _ (g, g₁)) :=
  by
  intro D T L sc G μ₀ hL W t i j A A₁ AV AV₁ hA hA₁ hV hV₁
  refine ⟨GlobalTheory.T.isSeesawHermitianTriple_gridSquare_of_standing hL W t i j, fun ωA ωB hωA hωB => ⟨fun x => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV G i j x.1 * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV₁ G t i j x.2,
    fun B ρ Θ Θ' hΘ => ?_⟩⟩
  have kA := GlobalTheory.T.thetaGridRouteKernel_eq_detCharacters_mul_thetaKernel hL W t i j ωA hωA B ρ Θ Θ' hΘ
  have kB := GlobalTheory.T.smallRoute_kernel_eq_char_mul_thetaKernel hL W t i j ωB hωB B ρ Θ Θ' hΘ
  have tr : ∀ (z : GA D (G.V (.grid ↑i ↑j)) →₀ ℂ) g g₁ u, translates z (kerSmall W Θ' g g₁) u =
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV G i j g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV₁ G t i j g₁) * thetaKO ωB u (GlobalTheory.SquareComm.blk _ _ (g, g₁))
        (GlobalTheory.SquareDict.zact ωB z (GlobalTheory.SquareDict.datumB W Θ')) := by
    intro z g g₁ u

    simp only [translates, kB, GlobalTheory.SquareDict.zact, thetaKO, Finsupp.sum, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e : ωB (u * k, GlobalTheory.SquareComm.blk _ _ (g, g₁)) = ωB (u, GlobalTheory.SquareComm.blk _ _ (g, g₁)) * ωB (k, 1) := by
      rw [← map_mul]; simp
    rw [e, Module.End.mul_apply]; ring
  refine ⟨GlobalTheory.T.routeDatum_mem_algebraicVectors_grid_frames hL W t i j A AV AV₁ hA hV hV₁ B ρ Θ Θ' hΘ, GlobalTheory.T.smallRouteDatum_mem_algebraicVectors_grid_frames hL W t i j A₁ AV AV₁ hA₁ hV hV₁ B ρ Θ Θ' hΘ, kA, tr, ?_, ?_⟩
  · intro M g g₁
    simp only [kA, GlobalTheory.SquareComm.thetaInt]
    exact integral_const_mul _ _
  · intro M z g g₁
    simp only [tr, GlobalTheory.SquareComm.thetaInt]
    exact integral_const_mul _ _

end GlobalTheory.SquareDict

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option autoImplicit false

namespace GlobalTheory.HeckeReadProof

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues

theorem phiW_eq {D : D7} (T : CoreJ D) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R ((i : ℕ) + 1)) (h : GA D (Wc D i))
    (hx : (dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV h).1).dom) :
    phiW T i σ hV a f h = (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) *
      (T.cE ((i : ℕ) + 1) σ (dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) *
      toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f ((T.U ((i : ℕ) + 1) σ).un (dictW T i σ hV h).1 ⟨(dictW T i σ hV h).2, hx⟩)) := by
  show T.phiJ _ σ a f _ = _
  rw [CoreJ.phiJ_apply]
  simp only [Core.phiAd, Pi.smul_apply, smul_eq_mul, adel, rdU, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [dictW, castDict] at hx ⊢
  split_ifs with h1
  · ring
  · exact absurd hx h1

theorem heckeReadTie (hSL : ∀ D, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D) (hVF : ∀ D, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D) :
    GlobalTheory.HeckeSupSt.HeckeReadTie := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hlev hgrp hfam hmod hthP ht i σ hσ hV hpin
  intro P p k α Rc hs cq f g hf hg hr h
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  have hgood : GoodEmb T.Q.c σ := hσ ▸ T.toCore.good_σ₀
  obtain ⟨hx, -, -⟩ := exists_witness T i σ hV ht.laws.toLawsM hgood h
  obtain ⟨e, he⟩ := GlobalTheory.T.heckeReading_kernels_match_cosets_through_frame D GlobalTheory.HeckePointLaw.heckePointLaws (hSL D) (hVF D) G Pl0 T0 A T R F κ v₀ hlev hgrp hfam
    hmod hthP ht i σ hσ hV hpin P p k α Rc hs h hx
  have hfin : Finite (hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ)
      ((T.U ((i : ℕ) + 1) σ).un (dictW T i σ hV h).1 ⟨(dictW T i σ hV h).2, hx⟩)) := Finite.of_equiv _ e.symm
  rw [phiW_eq T i σ hV _ g h hx]
  have hr' := hr (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (dictW T i σ hV h).1 ⟨(dictW T i σ hV h).2, hx⟩)
  have e1 : toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c g
      ((T.U ((i : ℕ) + 1) σ).un (dictW T i σ hV h).1 ⟨(dictW T i σ hV h).2, hx⟩)) =
      σ cq * σ (hkScal T.Q.c 1 P.asIdeal k D.R.nV) * ∑ᶠ C,
        toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f (he C).1.choose) := by
    refine (congrArg toC hr').trans ?_
    have hs1 : σ (hkScal T.Q.c cq P.asIdeal k D.R.nV) = σ cq * σ (hkScal T.Q.c 1 P.asIdeal k D.R.nV) := by
      simp only [hkScal, one_mul, map_mul]
    show σ (hkScal T.Q.c cq P.asIdeal k D.R.nV) * toC (hkVal _ _ _ _ f _) = _
    rw [hs1]
    congr 1
    unfold hkVal
    show (∑ᶠ C, toC (hkTerm _ _ _ _ f _ C)) = _
    refine finsum_congr fun C => ?_
    unfold hkTerm
    split_ifs with h1
    · rfl
    · exact absurd (he C).1 h1
  rw [e1]
  have e2 : ∀ C, (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
      (T.cE ((i : ℕ) + 1) σ (dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) *
      σ (hkScal T.Q.c 1 P.asIdeal k D.R.nV) * toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f (he C).1.choose) =
      (muAt T R i P)⁻¹ ^ k * phiW T i σ hV (wtA (κ i)) f (h * (e C : GA D (Wc D i))) :=
    fun C => (he C).2 _ (he C).1.choose_spec f hf
  have e3 : ∑ᶠ C, (muAt T R i P)⁻¹ ^ k * phiW T i σ hV (wtA (κ i)) f (h * (e C : GA D (Wc D i))) =
      (muAt T R i P)⁻¹ ^ k * ∑ a ∈ Rc, phiW T i σ hV (wtA (κ i)) f (h * a) := by
    rw [finsum_comp_equiv e (f := fun a : Rc =>
      (muAt T R i P)⁻¹ ^ k * phiW T i σ hV (wtA (κ i)) f (h * (a : GA D (Wc D i))))]
    rw [finsum_eq_sum_of_fintype, Finset.sum_coe_sort Rc
      (fun a => (muAt T R i P)⁻¹ ^ k * phiW T i σ hV (wtA (κ i)) f (h * a)), Finset.mul_sum]
  rw [mul_assoc (σ cq) ((muAt T R i P)⁻¹ ^ k), ← e3, ← finsum_congr e2, ← mul_finsum]
  ring

end GlobalTheory.HeckeReadProof
end
end
