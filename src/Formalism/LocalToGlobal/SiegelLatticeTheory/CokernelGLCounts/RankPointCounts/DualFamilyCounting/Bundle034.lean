module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle020
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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

namespace Formalism.L2.SG.Pf.NcIdx

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc
  Formalism.L2.SG.TypedSets MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

def IndexTypC : Prop :=
  ∀ p : TypX X,
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKnatp p /
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKp p =
      (gAt X p.1 : ℝ) ^ (-(((D.R.rS + 1) * (2 * D.R.k + 2 * D.R.rS + 1) : ℕ) : ℤ)) /
        aP (E := X.B.I.E) p.1 D.R.k X.B.I.n (Tw u)

end Formalism.L2.SG.Pf.NcIdx
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.NcReal

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.Volumes Formalism.L2.SG.LocVol
  NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.L2.SG.AdBridge
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D)

def AinfClause (ψ : AddChar (AF X.B.I.F) ℂ) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j) (a' : ℝ) : Prop :=
  AllSome (SdW X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (Ainf X.B.I.F) (psiInf X.B.I.F ψ) (D.R.rS + 1 + D.R.rS))
    fun μinf =>
  AllSome (SdHerm X.B.I.F X.B.I.E X.B.I.cm.sig (Ainf X.B.I.F) (psiInf X.B.I.F ψ) (D.R.rS + 1 + D.R.rS)) fun νinf =>
  AllSome (fun fibInf : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) →
        Measure (Fin (D.R.rS + 1 + D.R.rS) → Fin X.B.I.n → Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) =>
      IsFibreFamily μinf (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) Subtype.val
        {Y | LinearIndependent (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) Y} νinf Set.univ fibInf) fun fibInf =>
  ∀ f : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J → ENNReal, Measurable f →
    ∀ s : (Fin (D.R.rS + 1 + D.R.rS) → Fin X.B.I.n → Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J,
      (∀ y, (∃ g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J, g • ratTup (Ainf X.B.I.F) (tupH (frameOf X u')) = y) →
        s y • ratTup (Ainf X.B.I.F) (tupH (frameOf X u')) = y) →
      ∫⁻ g, f g ∂X.measG.μGinf = ENNReal.ofReal a' *
        ∫⁻ y, ∫⁻ h', f (s y * (h' : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) ∂(X.measW u').μHinf
          ∂(fibInf (hermOf (Ainf X.B.I.F) X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))) hT))

def eDF (k r : ℕ) : ℝ := -((8 * (r : ℝ) ^ 3 + 6 * (r : ℝ) ^ 2 + 6 * (k : ℝ) * (r : ℝ) ^ 2 + (r : ℝ)) / 3)

def RealBracket : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
    (ψ : AddChar (AF X.B.I.F) ℂ),
    HypX X hb FdN FdN' u u' → Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ → IsStdChar ψ →
    ∀ (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
        gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j) (a' : ℝ), 0 < a' → AinfClause X ψ u' hT a' →
    Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * (X.muH u Set.univ).toReal * (X.muN u FdN).toReal * (X.muN u' FdN').toReal =
      a' * 2 ^ (D.R.k * Fintype.card (InfinitePlace X.B.I.F)) *
        (Real.pi ^ D.R.k / ((D.R.k - 1).factorial : ℝ)) ^ Fintype.card (InfinitePlace X.B.I.F) *
        Formalism.L2.SG.RealObj.Tw u ^ (-((D.R.k * Fintype.card (InfinitePlace X.B.I.F) : ℕ) : ℤ)) *
        |(NumberField.discr X.B.I.F : ℝ)| ^ eDF D.R.k D.R.rS

end Formalism.L2.SG.Pf.NcReal
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.NcAsm

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

def NcValueC : Prop :=
  Formalism.L2.SG.Pf.Cnt.cExpl D F0 what₂ * (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).al =
    Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volH *
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN *
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN' *
      ((bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).unitLevelVolume /
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volZZ) *
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKnat /
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μH' * ngFac D

theorem ncTieC_of
    (hP : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Pos)
    (hM : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMass)
    (hMs : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMasses)
    (hL : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InLevelS)
    (hO : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InOrdinary)
    (hT : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InTyped)
    (hV : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InVolumes)
    (hVG : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volHa' =
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volG)
    (hCoo : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Coo =
      Formalism.L2.SG.MassDataConc.kapN D * Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1)
    (hkap : Formalism.L2.SG.MassDataConc.kapN D ≠ 0)
    (hval : NcValueC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq) :
    NcTieC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq (Formalism.L2.SG.Pf.Cnt.cExpl D F0 what₂) := by
  unfold NcTieC
  set B := bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq with hB
  rw [Formalism.L2.SG.Pf.NcCut.nc_iff B hP hM hMs hL hO hT ⟨hV.2.1, hV.2.2⟩ _ (ngFac D) (Formalism.L2.SG.MassDataConc.kapN D) hkap]
  have hG : 0 < B.volG := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hHa : 0 < B.volHa := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hBH : B.volB / B.volHa = 1 := by
    have h1 := hV.1
    rw [hVG] at h1
    have : B.volB = B.volHa := by
      have := mul_right_cancel₀ hG.ne' h1
      exact this
    rw [this, div_self hHa.ne']
  rw [hBH, hCoo]
  unfold NcValueC at hval
  rw [← hB] at hval
  linear_combination (Formalism.L2.SG.MassDataConc.kapN D) * hval

theorem kapN_ne (D : D7) : Formalism.L2.SG.MassDataConc.kapN D ≠ 0 := by
  unfold Formalism.L2.SG.MassDataConc.kapN
  have h1 := (Formalism.BasicNotions.rdE_pos_le D).1
  have hg : (0 : ℝ) < (Formalism.MainNotions.S.Lat.gS D : ℝ) := by
    have h0 := (D.host.g_prime 0).pos
    have h1' := (D.host.g_prime 1).pos
    unfold Formalism.MainNotions.S.Lat.gS
    exact_mod_cast Nat.mul_pos h0 h1'
  exact mul_ne_zero (pow_ne_zero _ h1.ne') (inv_ne_zero (pow_ne_zero _ hg.ne'))

theorem coo_bCF : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Coo =
    Formalism.L2.SG.MassDataConc.kapN D * Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 := rfl

theorem ncTieC_of'
    (hP : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Pos)
    (hM : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMass)
    (hMs : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMasses)
    (hL : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InLevelS)
    (hO : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InOrdinary)
    (hT : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InTyped)
    (hV : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InVolumes)
    (hVG : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volHa' =
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volG)
    (hval : NcValueC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq) :
    NcTieC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq (Formalism.L2.SG.Pf.Cnt.cExpl D F0 what₂) :=
  ncTieC_of X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hP hM hMs hL hO hT hV hVG
    (coo_bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq) (kapN_ne D) hval

end Formalism.L2.SG.Pf.NcAsm
end
end
