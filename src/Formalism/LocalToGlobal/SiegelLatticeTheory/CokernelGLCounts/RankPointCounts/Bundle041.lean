module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle036
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle038
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle039
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle037
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DataCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle027
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle036
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.TermsAtFiniteOf
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle034
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField

namespace Formalism.L2.SG.RhoPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Final

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem weight_eq (hR : IsRowReps D (X.Fu u) what₂) (hL : LatRowLat X u) (h : Hfin X u) :
    ((Nat.card ↥(gamR X u ⊓ (kR X u).map (MulAut.conj h).toMonoidHom) : ℕ) : ℝ)⁻¹ =
      wRow D (X.Fu u) (cls X u what₂ h) := by
  obtain ⟨-, δ, hδ, hδe⟩ := cls_spec hR hL h
  have e1 : Nat.card ↥(gamR X u ⊓ (kR X u).map (MulAut.conj h).toMonoidHom) =
      Nat.card ↥(autLz D (X.Fu u) (cls X u what₂ h)) := by
    rw [show gamR X u ⊓ (kR X u).map (MulAut.conj h).toMonoidHom = stabR X u h from rfl, card_stab, card_AH,
      ← hδe, card_autLz_gmap (X.Fu u) hδ]
  rw [e1]
  rfl

theorem massH_rows (hR : IsRowReps D (X.Fu u) what₂) (hL : LatRowLat X u) (hI : LatInj X u) (hS : LatSurj X u) :
    Formalism.L2.SG.TypedSets.massH X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (Formalism.L2.SG.TypedSets.frameOf X u) =
      Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) what₂ := by
  rw [massH_eq]
  exact massCl_eq_sum (gamR X u) (kR X u) what₂ (cls X u what₂) (wRow D (X.Fu u))
    (fun h => (cls_spec hR hL h).1) (cls_rel hR hL hI) (cls_surj hR hL hS) (weight_eq X u what₂ hR hL)

end Final

end Formalism.L2.SG.RhoPf

namespace Formalism.L2.SG.MassDataConc

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.Full MeasureTheory

theorem RhoTieC_holds {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    (sd C Th : ℝ) (vR : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
    (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp) (i0 i0' : NumberField.InfinitePlace X.B.I.F → Fin D.R.k)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hL : Formalism.L2.SG.Pf.LatRowLat X u) (hI : Formalism.L2.SG.Pf.LatInj X u) (hS : Formalism.L2.SG.Pf.LatSurj X u) :
    RhoTieC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq :=
  Formalism.L2.SG.RhoPf.massH_rows X u (Y.what₂ u) (Y.rowsOK u) hL hI hS

end Formalism.L2.SG.MassDataConc
end
end

section

noncomputable section

namespace Formalism.L2.SG.IntegralApproximation

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.MassDataConc MeasureTheory
open scoped Classical

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

theorem Gam1TieC_holds (Y : Formalism.L2.SG.Full.Full X) :
    LevelOneLatticeAgreement X hb hK FdN FdN' u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq := by
  unfold LevelOneLatticeAgreement
  show Formalism.L2.SG.TermOp.Gam1 Y.TR = _
  rw [Formalism.L2.SG.Pf.gamma_one_typed_places_holds X Y.TR]
  rfl

end Formalism.L2.SG.IntegralApproximation
end
end

section

noncomputable section

namespace Formalism.L2.SG.LsDatumB

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut MeasureTheory
open Classical ValuativeRel

section Cut

variable {D : Formalism.BasicNotions.D7}

def LocOrbSum (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 →
  ∀ (p : PlF D) (τ : Option ((M p).Cls D.R.rS)),
    HasSum (fL M δ (D.mem u).A.T (D.mem u').A.T p w τ) (BBtop M δ (D.mem u).A.T (D.mem u').A.T p w τ) ∧
    Summable (fun O => ‖fL M δ (D.mem u).A.T (D.mem u').A.T p w τ O‖) ∧
    (τ ≠ none → HasSum (gL M δ (D.mem u).A.T (D.mem u').A.T p w τ)
      (BBtop M δ (D.mem u).A.T (D.mem u').A.T p w τ / Pf.autP M p τ) ∧
    Summable (fun O => ‖gL M δ (D.mem u).A.T (D.mem u').A.T p w τ O‖))

def LocUnram (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (θ0 : ∀ p, Option ((M p).Cls D.R.rS)) : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 →
  ∃ S : Finset (PlF D), ∀ p ∉ S, Pf.autP M p (θ0 p) = 1 ∧
    ∀ (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)),
      fL M δ (D.mem u).A.T (D.mem u').A.T p w τ O =
          (if O = x0L M δ (D.mem u).A.T (D.mem u').A.T p w ∧ τ = θ0 p then 1 else 0) ∧
      gL M δ (D.mem u).A.T (D.mem u').A.T p w τ O =
          (if O = x0L M δ (D.mem u).A.T (D.mem u').A.T p w ∧ τ = θ0 p then 1 else 0)

def ThRestricted (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (θ0 : ∀ p, Option ((M p).Cls D.R.rS)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w → Pf.Restricted θ0 (thT M δ γ)

def ThSome (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w → ∀ p, thT M δ γ p ≠ none

def ScalKind (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ γ' : TermDef.Term D u u' F0 what₂) (w w' : Point D.host.E (D.R.rS + 1)), EligAt γ w → EligAt γ' w' →
    Corank.TermScal D γ γ' → kind w = kind w'

def EligFinite (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), {γ : TermDef.Term D u u' F0 what₂ | EligAt γ w}.Finite

def AtPtG (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), γ.atPt w →
    Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0

def PartnerTupleSum (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
  ∀ w' : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w' ≠ 0 → kind w' = kind w →
    (∀ γ' : TermDef.Term D u u' F0 what₂, Corank.TermScal D γ γ' → EligAt γ' w' →
      {p | locT M δ γ' p ≠ x0L M δ (D.mem u).A.T (D.mem u').A.T p w'}.Finite) ∧
    ∀ x : Rst (fun p => x0L M δ (D.mem u).A.T (D.mem u').A.T p w'),
      HasSum (fun γ' : {γ' : TermDef.Term D u u' F0 what₂ //
          (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = x.1} =>
          PairVal.cAt (PairVal.vRdef D u u' F0 what₂ δ M) γ'.1 w')
        (∏ᶠ p, fL M δ (D.mem u).A.T (D.mem u').A.T p w' (thT M δ γ p) (x.1 p))

def FiberTupleSum (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (L : CntLocal.LocSp D M) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ nc : ℝ, CntLocal.Formula δ L u u' F0 what₂ nc →
  ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
  ∀ w : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 →
  ∀ (γ₀ : TermDef.Term D u u' F0 what₂) (w₀ : Point D.host.E (D.R.rS + 1)), EligAt γ₀ w₀ → kind w = kind w₀ →
    (∀ γ : TermDef.Term D u u' F0 what₂, EligAt γ w →
      {p | locT M δ γ p ≠ x0L M δ (D.mem u).A.T (D.mem u').A.T p w}.Finite) ∧
    ∀ x : Rst (fun p => x0L M δ (D.mem u).A.T (D.mem u').A.T p w),
      HasSum (fun γ : {γ : TermDef.Term D u u' F0 what₂ //
          (EligAt γ w ∧ kind w = kind w₀ ∧ thT M δ γ = thT M δ γ₀) ∧ locT M δ γ = x.1} =>
          (PairVal.massTerm γ.1 : ℂ) * PairVal.cAt (PairVal.vRdef D u u' F0 what₂ δ M) γ.1 w)
        ((n0 nc (D.mem u).A.T (D.mem u').A.T w : ℂ) * (dnT M δ L ϖ γ₀ : ℂ) *
          ∏ᶠ p, gL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p))

def CoefProd (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
    PairVal.cAt (PairVal.vRdef D u u' F0 what₂ δ M) γ w =
      (∏ᶠ p, hL M δ (D.mem u).A.T (D.mem u').A.T p w (locT M δ γ p)) *
        ((PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard : ℂ)

def PartnerCount (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
  ∀ w' : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w' ≠ 0 → kind w' = kind w →
    (∀ γ' : TermDef.Term D u u' F0 what₂, Corank.TermScal D γ γ' → EligAt γ' w' →
      {p | locT M δ γ' p ≠ x0L M δ (D.mem u).A.T (D.mem u').A.T p w'}.Finite) ∧
    ∀ x : Rst (fun p => x0L M δ (D.mem u).A.T (D.mem u').A.T p w'),
      HasSum (fun γ' : {γ' : TermDef.Term D u u' F0 what₂ //
          (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = x.1} =>
          ((PairVal.orbT D u u' F0 what₂ γ'.1 (zT γ'.1)).ncard : ℂ))
        (∏ᶠ p, kL M δ (D.mem u).A.T (D.mem u').A.T p w' (thT M δ γ p) (x.1 p))

def FiberCount (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (L : CntLocal.LocSp D M) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ nc : ℝ, CntLocal.Formula δ L u u' F0 what₂ nc →
  ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
  ∀ w : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 →
  ∀ (γ₀ : TermDef.Term D u u' F0 what₂) (w₀ : Point D.host.E (D.R.rS + 1)), EligAt γ₀ w₀ → kind w = kind w₀ →
    (∀ γ : TermDef.Term D u u' F0 what₂, EligAt γ w →
      {p | locT M δ γ p ≠ x0L M δ (D.mem u).A.T (D.mem u').A.T p w}.Finite) ∧
    ∀ x : Rst (fun p => x0L M δ (D.mem u).A.T (D.mem u').A.T p w),
      HasSum (fun γ : {γ : TermDef.Term D u u' F0 what₂ //
          (EligAt γ w ∧ kind w = kind w₀ ∧ thT M δ γ = thT M δ γ₀) ∧ locT M δ γ = x.1} =>
          (PairVal.massTerm γ.1 : ℂ) * ((PairVal.orbT D u u' F0 what₂ γ.1 (zT γ.1)).ncard : ℂ))
        ((n0 nc (D.mem u).A.T (D.mem u').A.T w : ℂ) * (dnT M δ L ϖ γ₀ : ℂ) *
          ∏ᶠ p, eL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p))

def DnInDens (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
    ∃ Λ ∈ what₂, (CntLocal.EZ (CntLocal.Tn u') F0 Λ (zT γ)).Nonempty

def NormRepElig (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
    ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D ×
      PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2

def CutAt (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (L : CntLocal.LocSp D M) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  LocOrbSum M δ u u' ∧ ScalKind u u' F0 what₂ ∧
    CoefProd M δ u u' F0 what₂ ∧ PartnerCount M δ u u' F0 what₂ ∧ FiberCount M δ L u u' F0 what₂ ∧
    NormRepElig u u' F0 what₂ ∧ ThSome M δ u u' F0 what₂ ∧
    ∃ θ0 : ∀ p, Option ((M p).Cls D.R.rS), LocUnram M δ u u' θ0 ∧ ThRestricted M δ u u' F0 what₂ θ0

end Cut

end Formalism.L2.SG.LsDatumB
end
end

section

noncomputable section

namespace Formalism.L2.SG.DataCut

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.FourierDecayAlt Formalism.L2.SG.DataInst
open Classical ValuativeRel
open scoped ComplexOrder

def RowsDatumP (D : Formalism.BasicNotions.D7) : Prop :=
  (VS D).SigOK →
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : CntLocal.LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] → Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u') →
    ∀ (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ →
    ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
    ∀ nc : ℝ, CntLocal.Formula δ L u u' F0 what₂ nc →
      (∀ d ∈ densSet L δ ϖ u u' F0 what₂, 0 ≤ d) ∧
      ∃ (th : TermDef.Term D u u' F0 what₂ → ∀ p, Option ((M p).Cls D.R.rS)) (dn : TermDef.Term D u u' F0 what₂ → ℝ),
        (∀ θ0 : ∀ p, Option ((M p).Cls D.R.rS),
          (∀ w, ∃ S : Finset (PlF D), Formalism.L2.SG.Pf.UnramOff M δ (D.mem u).A.T (D.mem u').A.T θ0 S w) →
          ∀ γ w, EligAt γ w → Formalism.L2.SG.Pf.Restricted θ0 (th γ)) ∧
        (∀ γ w, EligAt γ w → dn γ ∈ densSet L δ ϖ u u' F0 what₂) ∧
        PartnerSumC δ M (PairVal.vRdef D u u' F0 what₂ δ M) th ∧
        FiberCntC δ M (PairVal.vRdef D u u' F0 what₂ δ M) nc th dn

def RowsDomAtP (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (Wp Wq : InfinitePlace D.host.E → Type) [∀ x, NormedAddCommGroup (Wp x)]
    [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting D.host.E Wp Wq) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep), (∀ p, Agree δ M p) →
    ∀ (L : CntLocal.LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] → Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u') → Compat S u u' →
    ∀ (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ →
    ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
    ∀ nc : ℝ, CntLocal.Formula δ L u u' F0 what₂ nc → ∀ α : ℝ, 0 < α →
    BddAbove (densSet L δ ϖ u u' F0 what₂) →
    ∀ κ : TermDef.Term D u u' F0 what₂ → ℕ, RowLabel κ →
    ∀ Y : Finset (TB.Pt D.host.E), (∀ p ∈ Y, TB.IsPt p ((dOf S δ M u u').r + 1)) →
      TB.PSDOn Y (fun p q => ((supDens L δ ϖ u u' F0 what₂ / α : ℝ) : ℂ) *
          (dOf S δ M u u').Kr ((dOf S δ M u u').r + 1) p q -
        rowKer (PairVal.vRdef D u u' F0 what₂ δ M) κ (nc * α) p q)

def RowsInputP (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (Wp Wq : InfinitePlace D.host.E → Type) [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting D.host.E Wp Wq) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep), (∀ p, Agree δ M p) →
    ∀ (L : CntLocal.LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] → Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u') → Compat S u u' →
    ∀ (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ →
    ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
    ∀ nc : ℝ, CntLocal.Formula δ L u u' F0 what₂ nc → ∀ α : ℝ, 0 < α →
    BddAbove (densSet L δ ϖ u u' F0 what₂) →
      (∃ κ : TermDef.Term D u u' F0 what₂ → ℕ, RowLabel κ) ∧
      ∀ κ : TermDef.Term D u u' F0 what₂ → ℕ, RowLabel κ →
        RowsPSD S δ M L u u' F0 what₂ ϖ (PairVal.vRdef D u u' F0 what₂ δ M) κ nc α

section P

variable {D : Formalism.BasicNotions.D7}

theorem rowsDomAtP_of (hN : SupportG.NormProd D) (hTU : TopUnram D) (hRD : RowsDatumP D)
    (hTF : ∀ u u' : D.what₂.Word, TermDef.TermsAtFinite D u u') (hsig : (VS D).SigOK) : RowsDomAtP D := by
  classical
  intro Wp Wq _ _ _ _ S δ M hA L u u' hT hPH hC F0 what₂ hrows ϖ hϖ nc hnc α hα hbdd κ hκ Y hY
  obtain ⟨hdens0, th, dn, hres, hdnS, hPS, hFC⟩ := hRD hsig δ M hA L u u' hT hPH F0 what₂ hrows ϖ hϖ nc hnc
  obtain ⟨θ0, hU⟩ := hTU δ M hA (D.mem u).A.T (D.mem u').A.T
  set sd := supDens L δ ϖ u u' F0 what₂ with hsdd
  have hsd0 : 0 ≤ sd := Real.sSup_nonneg (fun d hd => hdens0 d hd)
  have hdn : ∀ γ w, EligAt γ w → dn γ ≤ sd := fun γ w h => le_csSup hbdd (hdnS γ w h)
  have hFC' : FiberCntC δ M (PairVal.vRdef D u u' F0 what₂ δ M) (nc * α) th (fun γ => dn γ / α) := by
    intro w hG γ₀ w₀ h0
    have e : (n0 (nc * α) (D.mem u).A.T (D.mem u').A.T w : ℂ) * ((dn γ₀ / α : ℝ) : ℂ) =
        (n0 nc (D.mem u).A.T (D.mem u').A.T w : ℂ) * (dn γ₀ : ℂ) := by
      unfold n0
      push_cast
      field_simp
      try ring
    rw [e]
    exact hFC w hG γ₀ w₀ h0
  have hnc' : 0 < nc * α := mul_pos hnc.1 hα

  let pt0 : Point D.host.E (D.R.rS + 1) := ⟨[(1, D.R.rS + 1)], by simp, by simp⟩
  let wOf : Y → Point D.host.E (D.R.rS + 1) := fun x => (ptOfList (D.R.rS + 1) x.1).getD pt0
  have hP := dom_points hN hA hrows hnc' (PairVal.vRdef D u u' F0 what₂ δ M) hκ (hTF u u') hsig hU (hres θ0 (fun w => (hU w).1))
    (sd / α) (div_nonneg hsd0 hα.le) (fun γ w h => div_le_div_of_nonneg_right (hdn γ w h) hα.le) hPS hFC' wOf
  let φi : Y → ℂ := fun x => if (ptOfList (D.R.rS + 1) x.1).isSome then ((phi (D.R.rS + 1) x.1 : ℝ) : ℂ)⁻¹ else 0
  have hr : (dOf S δ M u u').r = D.R.rS := hC.1
  unfold TB.PSDOn
  rw [hr]
  have key : (Matrix.of fun x y : Y => ((sd / α : ℝ) : ℂ) * (dOf S δ M u u').Kr (D.R.rS + 1) x.1 y.1 -
      rowKer (PairVal.vRdef D u u' F0 what₂ δ M) κ (nc * α) x.1 y.1) =
      (Matrix.diagonal φi).conjTranspose * (Matrix.of fun x y : Y => ((sd / α : ℝ) : ℂ) *
        KtopG M δ (D.mem u).A.T (D.mem u').A.T (wOf x) (wOf y) -
        ∑' ρ, chat (PairVal.vRdef D u u' F0 what₂ δ M) κ (nc * α) ρ (wOf x) *
          star (chat (PairVal.vRdef D u u' F0 what₂ δ M) κ (nc * α) ρ (wOf y))) * Matrix.diagonal φi := by
    ext x y
    rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply, Matrix.of_apply]
    show _ = star (φi x) * _ * φi y
    rcases hx : ptOfList (D.R.rS + 1) x.1 with _ | wx
    · have h0 : φi x = 0 := by simp [φi, hx]
      rw [h0, star_zero, zero_mul, zero_mul]
      have hK : (dOf S δ M u u').Kr (D.R.rS + 1) x.1 y.1 = 0 := by
        show KrOf δ M (D.mem u).A.T (D.mem u').A.T (D.R.rS + 1) x.1 y.1 = 0
        unfold KrOf
        rw [if_neg (Nat.succ_ne_zero _), if_neg (lt_irrefl _), hx]
      have hR : rowKer (PairVal.vRdef D u u' F0 what₂ δ M) κ (nc * α) x.1 y.1 = 0 := by
        unfold rowKer
        simp [rowVec, hx]
      rw [hK, hR]
      simp
    rcases hy : ptOfList (D.R.rS + 1) y.1 with _ | wy
    · have h0 : φi y = 0 := by simp [φi, hy]
      rw [h0, mul_zero]
      have hK : (dOf S δ M u u').Kr (D.R.rS + 1) x.1 y.1 = 0 := by
        show KrOf δ M (D.mem u).A.T (D.mem u').A.T (D.R.rS + 1) x.1 y.1 = 0
        unfold KrOf
        rw [if_neg (Nat.succ_ne_zero _), if_neg (lt_irrefl _), hx, hy]
      have hR : rowKer (PairVal.vRdef D u u' F0 what₂ δ M) κ (nc * α) x.1 y.1 = 0 := by
        unfold rowKer
        simp [rowVec, hy]
      rw [hK, hR]
      simp
    have hwx : wOf x = wx := by simp [wOf, hx]
    have hwy : wOf y = wy := by simp [wOf, hy]
    have hφx : φi x = ((phi (D.R.rS + 1) x.1 : ℝ) : ℂ)⁻¹ := by simp [φi, hx]
    have hφy : φi y = ((phi (D.R.rS + 1) y.1 : ℝ) : ℂ)⁻¹ := by simp [φi, hy]
    have hx' : Formalism.L2.S.IsPtL x.1 (D.R.rS + 1) := by
      by_contra hn
      simp [ptOfList, isPtL_signPt, hn] at hx
    have hy' : Formalism.L2.S.IsPtL y.1 (D.R.rS + 1) := by
      by_contra hn
      simp [ptOfList, isPtL_signPt, hn] at hy
    have hpx : ((phi (D.R.rS + 1) x.1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (phi_pos hx').ne'
    have hpy : ((phi (D.R.rS + 1) y.1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (phi_pos hy').ne'
    have hK : (dOf S δ M u u').Kr (D.R.rS + 1) x.1 y.1 = KtopG M δ (D.mem u).A.T (D.mem u').A.T wx wy /
        (((phi (D.R.rS + 1) x.1 : ℝ) : ℂ) * ((phi (D.R.rS + 1) y.1 : ℝ) : ℂ)) := by
      show KrOf δ M (D.mem u).A.T (D.mem u').A.T (D.R.rS + 1) x.1 y.1 = _
      unfold KrOf
      rw [if_neg (Nat.succ_ne_zero _), if_neg (lt_irrefl _), hx, hy]
      simp only
      rw [Kglob, dite_eq_left rfl]
    have hR : rowKer (PairVal.vRdef D u u' F0 what₂ δ M) κ (nc * α) x.1 y.1 =
        (∑' ρ, chat (PairVal.vRdef D u u' F0 what₂ δ M) κ (nc * α) ρ wx *
          star (chat (PairVal.vRdef D u u' F0 what₂ δ M) κ (nc * α) ρ wy)) /
        (((phi (D.R.rS + 1) x.1 : ℝ) : ℂ) * ((phi (D.R.rS + 1) y.1 : ℝ) : ℂ)) := by
      unfold rowKer
      rw [← tsum_div_const]
      refine tsum_congr fun ρ => ?_
      rw [rowVec_eq_chat _ _ _ ρ x.1 wx hx, rowVec_eq_chat _ _ _ ρ y.1 wy hy]
      simp only [Complex.star_def, map_div₀, Complex.conj_ofReal]
      field_simp
    rw [hK, hR, hwx, hwy, hφx, hφy]
    simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal]
    field_simp
  rw [key]
  exact hP.conjTranspose_mul_mul_same _

theorem rowsInputP_of (hG : Corank.ScalarEquivG) (hR : ∀ u u' : D.what₂.Word, Corank.ScalarRepFree D u u')
    (hF : RowsFinAt D) (hDm : RowsDomAtP D) : RowsInputP D := by
  intro Wp Wq _ _ _ _ S δ M hA L u u' hT hPH hC F0 what₂ hrows ϖ hϖ nc hnc α hα hbdd
  refine ⟨rowLabelExists_of hG hR u u' F0 what₂ hrows, fun κ hκ => ?_⟩
  intro Y hY R
  exact psdOn_of_full Y _ _ (fun x => hF δ M hA u u' hT F0 what₂ hrows (nc * α) κ hκ x)
    (hDm Wp Wq S δ M hA L u u' hT hPH hC F0 what₂ hrows ϖ hϖ nc hnc α hα hbdd κ hκ Y hY) R

theorem rowsInputP_of_termsFinite_sig (hN : SupportG.NormProd D) (hTU : TopUnram D) (hRD : RowsDatumP D)
    (hTF : ∀ u u' : D.what₂.Word, TermDef.TermsAtFinite D u u') (hsig : (VS D).SigOK) : RowsInputP D :=
  rowsInputP_of Formalism.L2.SG.Closed.ScalarEquivG_holds
    (fun u u' => Formalism.L2.SG.Closed.ScalarRepFree_holds (D := D) (u := u) (u' := u'))
    (rowsFinAt_of hTF hsig) (rowsDomAtP_of hN hTU hRD hTF hsig)

theorem rowsInputP_of_normProd_topUnram (hN : Formalism.L2.SG.SupportG.NormProd D) (hTU : TopUnram D) (hRD : RowsDatumP D) :
    RowsInputP D :=
  rowsInputP_of_termsFinite_sig hN hTU hRD (fun u u' => terms_at_point_finite D u u') (PI.TermsAtPtFiniteW.sigOK_holds D)

theorem rowsInputP_of_normProd (hN : Formalism.L2.SG.SupportG.NormProd D) (hRD : RowsDatumP D) : RowsInputP D :=
  rowsInputP_of_normProd_topUnram hN (Formalism.L2.SG.Pf.topUnram_holds D) hRD

end P

end Formalism.L2.SG.DataCut

namespace Formalism.L2.SG.LsDatumB

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
open Classical ValuativeRel

end Formalism.L2.SG.LsDatumB
end
end
