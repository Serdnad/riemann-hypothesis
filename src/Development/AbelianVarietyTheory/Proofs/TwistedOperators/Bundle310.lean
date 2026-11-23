module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle277
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InertPlaceHomLatticeComponentsScaledIntegral
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle281
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle283
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle292
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle296
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle269
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle293
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle234
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle336
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.inertPlace_homLattice_components_scaled_integral : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → IsInertAt D.host.F D.host.E v w → ∀ a : GL (Fin T.rank) (w.adicCompletion D.host.E), IsFrameAt w (frameLat T) a → ∃ (c₀ : w.adicCompletion D.host.E) (b : GL (Fin S.rank) (w.adicCompletion D.host.E)), c₀ ≠ 0 ∧ ∀ X : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E), X ∈ (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).toAddSubgroup.map (GlobalTheory.InertHomIdx.matW S T w) ↔ c₀ • ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * X * b.1) ∈ GlobalTheory.InertHomIdx.intMat (w.adicCompletion D.host.E) T.rank S.rank := by
  first | exact @GlobalTheory.InertHomLattice.mem_map_latF_iff | exact GlobalTheory.InertHomLattice.mem_map_latF_iff | (intros; apply GlobalTheory.InertHomLattice.mem_map_latF_iff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.otherInstanceCharacter_eq_conjInstancePsiValue_integral : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (κ : GA D (Yc D 0)), ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset → GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ X.chi2 ((iotaX X h).toMulEquiv κ).2 = GlobalTheory.SeeConjChar.chiS X h (GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ)) := by
  first | exact @GlobalTheory.SeeConjChar.argT_mem_intAf_and_chi2_eq_chiS_of_mem_Kset | exact GlobalTheory.SeeConjChar.argT_mem_intAf_and_chi2_eq_chiS_of_mem_Kset | (intros; apply GlobalTheory.SeeConjChar.argT_mem_intAf_and_chi2_eq_chiS_of_mem_Kset <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SeeConjRead

noncomputable section
namespace GlobalTheory.SeeConjChar
open Classical

theorem hT_pairAt_int : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ (PP : Pl D.host.E) (a : Fin (Yc D 0).rank) (z : Fin (Yc D 0).rank → EAf D), (∀ i, Matrix.mulVec (β⁻¹).val z i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → GlobalTheory.SeeConjChar.hT X h (pairAt X h PP a) z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D X h β hβ PP a z hz
  have hLf := GlobalTheory.KgFrame.Lf_eq D
  have hzL : z ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf := by
    rw [hLf]
    exact (hβ z).2 hz
  set S : Set (Fin (Yc D 0).rank → EAf D) := {v | v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf} with hS
  have h0 : (0 : Fin (Yc D 0).rank → EAf D) ∈ S := by
    show (0 : Fin (Yc D 0).rank → EAf D) ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf
    exact zero_mem _
  obtain ⟨hef, hz0, hbw⟩ := X.vectorsInLattice
  have he : ∀ a, e0T X h a ∈ S := GlobalTheory.SeeConjRead.cast_fun_mem_Lf h X.e0 (fun a => (hef a).1)
  have hf : ∀ a, f0T X h a ∈ S := GlobalTheory.SeeConjRead.cast_fun_mem_Lf h X.f0 (fun a => (hef a).2)
  have hb : ∀ a, bwT X h a ∈ S := GlobalTheory.SeeConjRead.cast_fun_mem_Lf h X.bw (fun a => (hbw a).1)
  have hbd : ∀ a, bwdT X h a ∈ S := GlobalTheory.SeeConjRead.cast_fun_mem_Lf h X.bwd (fun a => (hbw a).2)
  have hzz : z0T X h ∈ S := GlobalTheory.SeeConjRead.cast_mem_Lf h X.z0 hz0
  have hv : pairAt X h PP a ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf := by
    show pairAt X h PP a ∈ S
    unfold pairAt
    split_ifs
    · exact GlobalTheory.SeeConjRead.flagV_mem S h0 _ _ _ _ _ _ _ hf he hbd hzz a
    · exact GlobalTheory.SeeConjRead.flagV_mem S h0 _ _ _ _ _ _ _ hf he (fun i => hb _) hzz a
  unfold hT
  exact intAf_cast X h _ (Formalism.L2.SG.Pf.unitaryCongruence.hA_int _ (GlobalTheory.SeeConjRead.cast_mem_Lf h.symm _ hv)
    (GlobalTheory.SeeConjRead.cast_mem_Lf h.symm _ hzL))

end GlobalTheory.SeeConjChar
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowVertexInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def thetaSub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f}
  add_mem' := by
    intro f g hf hg
    obtain ⟨U₁, hU₁, h₁⟩ := hf.level
    obtain ⟨U₂, hU₂, h₂⟩ := hg.level
    refine ⟨fun γ w => ?_, ⟨U₁ ⊓ U₂, hU₁.inter hU₂, fun u hu hu0 => ?_⟩, hf.cont.add hg.cont,
      fun k L hL h0 w => (hf.smooth k L hL h0 w).add (hg.smooth k L hL h0 w)⟩
    · simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
    · funext w
      have e₁ := congrFun (h₁ u hu.1 hu0) w
      have e₂ := congrFun (h₂ u hu.2 hu0) w
      simp only [heisO, Pi.add_apply] at e₁ e₂ ⊢
      rw [mul_add, e₁, e₂]
  zero_mem' := ⟨fun γ w => by simp, ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun u _ _ => by funext w; simp [heisO]⟩, continuous_const,
    fun k L hL h0 w => contDiff_const⟩
  smul_mem' := by
    intro c f hf
    obtain ⟨U₁, hU₁, h₁⟩ := hf.level
    refine ⟨fun γ w => ?_, ⟨U₁, hU₁, fun u hu hu0 => ?_⟩, hf.cont.const_smul c,
      fun k L hL h0 w => (hf.smooth k L hL h0 w).const_smul c⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hf.quasi]; ring
    · funext w
      have e₁ := congrFun (h₁ u hu hu0) w
      simp only [heisO, Pi.smul_apply, smul_eq_mul] at e₁ ⊢
      rw [← e₁]; ring


variable (t : T) in
def positionPair (m : ℕ) : Fin m ⊕ Fin m → Pair T
  | .inl j => .top t j
  | .inr i => .chi i m


variable (G) in
abbrev FactorFn (t : T) (a : Fin D.R.m ⊕ Fin D.R.m) : Type :=
  WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) → ℂ

def vecOf (S : GridChoice W U) {t : T} (d : PureDat G t) : ∀ a, FactorFn G t a
  | .inl j => S.Z.vec (d.1 j)
  | .inr i => S.Z.vec (d.2 i)

def kkV (S : GridChoice W U) (p : Pair T) (f : WO (G.pS p) (G.pT p) → ℂ) (a : FinPt G p.small) (b : FinPt G p.big) :
    VV ℂ (wt G p.small) →ₗ[ℂ] VV ℂ (wt G p.big) :=
  S.Z.scal 1 p • fockComp W S.N.frC p f (a * S.N.u _) (b * S.N.u _)

def colV (S : GridChoice W U) {t : T} (v : ∀ a, FactorFn G t a) (x : ∀ j, FinPt G (.top j)) :
    VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (wt G (.top D.R.m)) :=
  chainTo (V := fun j => VV ℂ (wt G (.top j)))
    (fun j => if h : j < D.R.m then kkV S (.top t j) (v (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹

def rowV (S : GridChoice W U) {t : T} (v : ∀ a, FactorFn G t a) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] VV ℂ (wt G (.grid D.R.m D.R.m)) :=
  chainTo (V := fun i => VV ℂ (wt G (.grid i D.R.m)))
    (fun i => if h : i < D.R.m then kkV S (.chi i D.R.m) (v (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.grid 0 D.R.m))⁻¹ ∘ₗ funOf (listedWt G (.grid 0 D.R.m))

def pairFn (S : GridChoice W U) {t : T} (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m))
    (v : ∀ a, FactorFn G t a) : VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] ℂ :=
  (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂ (colV S v x) (rowV S v y)

theorem pairPts_eq_sum (S : GridChoice W U) {t : T} (τ : PureDat G t →₀ ℂ) (x : ∀ j, FinPt G (.top j))
    (y : ∀ i, FinPt G (.grid i D.R.m)) : pairPts S τ x y = τ.sum fun d c => c • pairFn S x y (vecOf S d) := rfl

def moved (S : GridChoice W U) (j : ℕ) (k : FinPt G (.grid (j + 1) D.R.m)) : GA D (G.V (.grid (j + 1) D.R.m)) :=
  ((S.N.u (.grid (j + 1) D.R.m))⁻¹ * k * S.N.u (.grid (j + 1) D.R.m) : FinPt G (.grid (j + 1) D.R.m))

def moveV (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (v : ∀ a, FactorFn G t a) : ∀ a, FactorFn G t a :=
  Function.update
    (Function.update v (.inr ⟨j, by omega⟩)
      (W.om (.chi j D.R.m) (G.toPair (.chi j D.R.m) 1 (moved S j k)) (v (.inr ⟨j, by omega⟩)) : FactorFn G t (.inr ⟨j, by omega⟩)))
    (.inr ⟨j + 1, hj⟩)
    (W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (v (.inr ⟨j + 1, hj⟩)) : FactorFn G t (.inr ⟨j + 1, hj⟩))

end GlobalTheory.RowVertexInv
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def colMapV (S : GridChoice W U) (t : T) (v : ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ)
    (x : ∀ j, FinPt G (.top j)) : VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (wt G (.top D.R.m)) :=
  chainTo (V := fun j => VV ℂ (wt G (.top j)))
    (fun j => if h : j < D.R.m then S.Z.scal 1 (.top t j) •
      fockComp W S.N.frC (.top t j) (v ⟨j, h⟩) (x j * S.N.u _) (x (j + 1) * S.N.u _) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹

def rowMapV (S : GridChoice W U) (v : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)
    (y : ∀ i, FinPt G (.grid i D.R.m)) : VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] VV ℂ (wt G (.grid D.R.m D.R.m)) :=
  chainTo (V := fun i => VV ℂ (wt G (.grid i D.R.m)))
    (fun i => if h : i < D.R.m then S.Z.scal 1 (.chi i D.R.m : Pair T) •
      fockComp W S.N.frC (.chi i D.R.m : Pair T) (v ⟨i, h⟩) (y i * S.N.u _) (y (i + 1) * S.N.u _) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.grid 0 D.R.m))⁻¹ ∘ₗ funOf (listedWt G (.grid 0 D.R.m))

def pairV (S : GridChoice W U) (t : T) {δ : Type} (τ : δ →₀ ℂ)
    (c : δ → ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ)
    (r : δ → ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)
    (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] ℂ :=
  τ.sum fun d a => a • (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂
    (colMapV S t (c d) x) (rowMapV S (r d) y)

theorem pairPts_eq_pairV (S : GridChoice W U) {t : T} (τ : PureDat G t →₀ ℂ) (x : ∀ j, FinPt G (.top j))
    (y : ∀ i, FinPt G (.grid i D.R.m)) :
    pairPts S τ x y = pairV S t τ (fun d j => S.Z.vec (d.1 j)) (fun d i => S.Z.vec (d.2 i)) x y := rfl

def movedCol (S : GridChoice W U) {t : T} (d : PureDat G t) (j : ℕ) (hj : j + 1 < D.R.m) (g : FinPt G (.top (j + 1))) :
    ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)) → ℂ :=
  Function.update (Function.update (fun j' => S.Z.vec (d.1 j')) ⟨j, by omega⟩
      (W.om (.top t j) (1, (g : GA D (G.V (.top (j + 1))))) (S.Z.vec (d.1 ⟨j, by omega⟩))))
    ⟨j + 1, hj⟩ (W.om (.top t (j + 1)) ((g : GA D (G.V (.top (j + 1)))), 1) (S.Z.vec (d.1 ⟨j + 1, hj⟩)))

end GlobalTheory.ExpansionInvariance

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopZeroInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

abbrev Arr (D : D7) : Type := Fin D.R.m ⊕ Fin D.R.m

def arrP (t : T) : Arr D → Pair T
  | .inl j => .top t j
  | .inr i => .chi i D.R.m


variable (G) in
abbrev Vecs (t : T) : Type := ∀ a : Arr D, WO (G.pS (arrP t a)) (G.pT (arrP t a)) → ℂ

def vecsOf (S : GridChoice W U) {t : T} (d : PureDat G t) : Vecs G t
  | .inl j => S.Z.vec (d.1 j)
  | .inr i => S.Z.vec (d.2 i)

def kkVec (S : GridChoice W U) (p : Pair T) (f : WO (G.pS p) (G.pT p) → ℂ) (x : FinPt G p.small) (y : FinPt G p.big) :
    VV ℂ (wt G p.small) →ₗ[ℂ] VV ℂ (wt G p.big) :=
  S.Z.scal 1 p • fockComp W S.N.frC p f (x * S.N.u _) (y * S.N.u _)

def colV (S : GridChoice W U) {t : T} (fs : Vecs G t) (x : ∀ j, FinPt G (.top j)) :
    VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (wt G (.top D.R.m)) :=
  chainTo (V := fun j => VV ℂ (wt G (.top j)))
    (fun j => if h : j < D.R.m then kkVec S (.top t j) (fs (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹

def rowV (S : GridChoice W U) {t : T} (fs : Vecs G t) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] VV ℂ (wt G (.grid D.R.m D.R.m)) :=
  chainTo (V := fun i => VV ℂ (wt G (.grid i D.R.m)))
    (fun i => if h : i < D.R.m then kkVec S (.chi i D.R.m) (fs (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.grid 0 D.R.m))⁻¹ ∘ₗ funOf (listedWt G (.grid 0 D.R.m))

def pairVec (S : GridChoice W U) {t : T} (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (fs : Vecs G t) :
    VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] ℂ :=
  (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂ (colV S fs x) (rowV S fs y)

theorem pairPts_eq (S : GridChoice W U) {t : T} (τ : PureDat G t →₀ ℂ) (x : ∀ j, FinPt G (.top j))
    (y : ∀ i, FinPt G (.grid i D.R.m)) (v w) :
    pairPts S τ x y v w = τ.sum fun d a => a * pairVec S x y (vecsOf S d) v w := by
  unfold pairPts Finsupp.sum
  rw [LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
  rfl

def first : Arr D := .inl ⟨0, by have := D.R.two_le_m; omega⟩

def moveFirst (W : G.Weil) {t : T} (g : FinPt G (.top 0)) (fs : Vecs G t) : Vecs G t :=
  Function.update fs first (W.om (.top t 0) (G.toPair (.top t 0) g.1 1) (fs first))

end GlobalTheory.TopZeroInv
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.gluedLattice_selfDual_primitive_meet : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V), IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V), Submodule.IsFullLattice D.host.E L₀ → IsGlueVec X u L₀ (vA X x₀) → IsSDIn Y (flatSp Y X ι z) (glueLat Y X ι z u L₀ x₀) ∧ IsPrim Y z (glueLat Y X ι z u L₀ x₀) ∧ capX Y X ι (glueLat Y X ι z u L₀ x₀) = L₀ := by
  first
  | exact @GlobalTheory.GlueVecLattice.glueLat_selfDual_prim_cap
  | intro D u Y X ι z h L₀ x₀ hL hg
    exact GlobalTheory.GlueVecLattice.glueLat_selfDual_prim_cap D u Y X ι z h L₀ x₀ hL.toIsLattice hg
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isAdelicGlueVector_of_selfDual_primitive : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V), IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V), Submodule.IsFullLattice D.host.E L₀ → IsSDIn Y (flatSp Y X ι z) (glueLat Y X ι z u L₀ x₀) → IsPrim Y z (glueLat Y X ι z u L₀ x₀) → IsGlueVec X u L₀ (vA X x₀) := by
  intro D u Y X ι z h L₀ x₀ hlat hSD hP
  letI := hlat
  exact GlobalTheory.AdIsom.SelfDualGlue.isGlueVec_of_isSDIn D u Y X ι z h L₀ x₀
    (by first | exact hlat | infer_instance) hSD hP
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.gluedLattice_prescribed_localComponents : ∀ (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V), IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V) (f₀ : Pl D.host.E → Fin X.rank → EAf D), Submodule.IsLattice D.host.E L₀ → IsGlueVec X u L₀ (vA X x₀) → (∀ w : Pl D.host.E, π ∈ w.asIdeal → idem w • f₀ w = f₀ w ∧ f₀ w - idem w • vA X x₀ ∈ hat L₀) → IsGlued Y X ι z u π L₀ f₀ (glueLat Y X ι z u L₀ x₀) := by
  first | exact @GlobalTheory.GluedCmp.isGlued_glueLat | exact GlobalTheory.GluedCmp.isGlued_glueLat | (intros; apply GlobalTheory.GluedCmp.isGlued_glueLat <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FinZeta.TrivCount

theorem trivial_isUnitarisable {G : Type} [Group G] :
    IsUnitarisable (Representation.trivial ℂ G ℂ) := by
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => x * starRingEnd ℂ y)
      (fun _ _ _ => add_mul _ _ _) (fun _ _ _ => by simp [mul_assoc])
      (fun _ _ _ => by simp [mul_add]) (fun _ _ _ => by simp [mul_left_comm]), ?_, ?_, ?_⟩
  · intro v w; simp [mul_comm]
  · intro v hv; simpa [Complex.mul_conj] using hv
  · intro g v w; simp

theorem heckeVec_trivial_dosetInd {G : Type} [Group G] {K : Subgroup G} (hK : IsCommensurated K) (t : G) :
    heckeVec (Representation.trivial ℂ G ℂ) K (dosetInd ℂ K t) 1 =
      ((Nat.card {a : G ⧸ K // a.out ∈ DoubleCoset.doubleCoset t (K : Set G) K} : ℝ) : ℂ) • 1 := by
  classical
  set D := DoubleCoset.doubleCoset t (K : Set G) K
  have hfin : {a : G ⧸ K | a.out ∈ D}.Finite := by
    refine (Formalism.UG.P.finite_support_cosets hK (Formalism.UG.Final.DosetIndMem G K ℂ t).2).subset ?_
    intro a ha
    have h' : a.out ∈ D := ha
    simp only [Set.mem_setOf_eq, dosetInd]
    rw [Set.indicator_of_mem h']
    simp
  have e : (fun c : G ⧸ K => dosetInd ℂ K t c.out • (Representation.trivial ℂ G ℂ) c.out (1 : ℂ)) =
      Set.indicator {a : G ⧸ K | a.out ∈ D} 1 := by
    funext c
    by_cases h : c.out ∈ D <;> simp [dosetInd, D, h, Set.indicator]
  rw [heckeVec, e, ← finsum_mem_def, finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hc : Nat.card {a : G ⧸ K // a.out ∈ D} = hfin.toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact Nat.card_coe_set_eq {a : G ⧸ K | a.out ∈ D}
  rw [hc]
  simp

theorem hasSum_card_cosets_diag : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ T : (Fin r → ℤ) → GL (Fin r) (w.adicCompletion E), (∀ d, (T d).1 = Matrix.diagonal fun i => ϖ ^ d i) → ∃ B₀ : Multiset ℂˣ, (∀ β ∈ B₀, ‖(β : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2)) ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ X : ℝ, 0 < X → X < δ → HasSum (fun d : {d : Fin r → ℤ // Antitone d} => ((Nat.card {a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r) // a.out ∈ DoubleCoset.doubleCoset (T d.1) (KGL w (n := r) : Set (GL (Fin r) (w.adicCompletion E))) (KGL w (n := r))} : ℝ) : ℂ) * (X : ℂ) ^ (∑ i, |d.1 i|).toNat) (eulerFac B₀ ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * eulerFac (B₀.map (·⁻¹)) ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * (X : ℂ) ^ 2)) := by
  intro hP E _ _ w r ϖ hϖ T hT
  have hK : IsCommensurated (KGL w (n := r)) := Formalism.UG.Final.GLintComm E w r
  let ρ := Representation.trivial ℂ (GL (Fin r) (w.adicCompletion E)) ℂ
  have hu : IsUnitarisable ρ := trivial_isUnitarisable
  have hfix : (1 : ℂ) ∈ fixed ρ (KGL w (n := r)) := GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl
  have heig : ∀ h ∈ Hecke ℂ (KGL w (n := r)), ∃ c : ℂ, heckeVec ρ (KGL w (n := r)) h 1 = c • (1 : ℂ) :=
    fun h _ => ⟨heckeVec ρ (KGL w (n := r)) h 1, by rw [smul_eq_mul, mul_one]⟩
  obtain ⟨B, hB, hbd⟩ := GlobalTheory.T.exists_satakeParam_trivialBound_unitaryGL E w r ℂ ρ hu 1 one_ne_zero hfix heig
  have hc : ∀ d, heckeVec ρ (KGL w (n := r)) (dosetInd ℂ (KGL w (n := r)) (T d)) 1 =
      (fun d => ((Nat.card {a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r) // a.out ∈
        DoubleCoset.doubleCoset (T d) (KGL w (n := r) : Set (GL (Fin r) (w.adicCompletion E))) (KGL w (n := r))} : ℝ) : ℂ)) d
        • (1 : ℂ) := fun d => heckeVec_trivial_dosetInd hK (T d)
  refine ⟨B, hbd, ?_⟩
  have key := GlobalTheory.T.hasSum_heckeEigenvalue_generatingSeries_GL hP E w r ℂ ρ 1 B hB ϖ hϖ T hT _ hc
  beta_reduce at key
  exact key

end GlobalTheory.FinZeta.TrivCount
end

section

open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.realPlacePoint_commute_of_ne_place : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ τ' : D.what₂.Tau), τ ≠ τ' → ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ'), atTau θ V τ g * atTau θ V τ' g' = atTau θ V τ' g' * atTau θ V τ g := by
  first | exact @GlobalTheory.PointAtPlaceComm.atTau_comm | exact GlobalTheory.PointAtPlaceComm.atTau_comm | (intros; apply GlobalTheory.PointAtPlaceComm.atTau_comm <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilCoeff

theorem heis_coeff_eq : ∀ (D : D7) (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (g : GA D V) (h : GA D W) (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∀ (μ₀ : Measure (WO V W)) (𝓕₀ : Set (WO V W)), μ₀.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕₀ μ₀ → ∀ w₀ : WO V W, ∫ w in 𝓕₀, heisO ψ V W (actO V W g h w₀) (ω (g, h) f) w * starRingEnd ℂ (ω (g, h) f w) ∂μ₀ = ∫ w in 𝓕₀, heisO ψ V W w₀ f w * starRingEnd ℂ (f w) ∂μ₀ := by
  intro D V W ψ χS χT ω hω g h f hf μ₀ 𝓕₀ hμ h𝓕 w₀
  have hf1 := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hω.std V W).1 w₀ f hf
  rw [← hω.om_heis g h w₀ f hf]
  exact GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hω.std V W μ₀ 𝓕₀ hμ h𝓕 (ω (g, h))
    (fun f hf => hω.om_pres (g, h) f hf) (fun f hf => hω.om_unit μ₀ 𝓕₀ hμ h𝓕 (g, h) f hf) _ f hf1 hf

end GlobalTheory.WeilCoeff
end
