module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActR
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle041
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BaseOfCore
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.QuotMeasExists
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemma3
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.AmpTensorDSdNonemptyOfSubsingleton
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.NumericSettingWithGapSatisfiable
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle026
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsColLatRepS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RightActionThreeFamilies
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle024
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle028
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle028
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NGClosed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle002
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open Formalism.L2.SG.RealObj.EnergyIntTor Formalism.L2.SG.Pf.WuBL
open scoped InnerProductSpace ENNReal

namespace Formalism.L2.SG.RealObj.EnergyIntLoc

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem cStd_ne : Formalism.QuantumDeterminants.cStd ≠ 0 := by
  simp [Formalism.QuantumDeterminants.cStd]

theorem muNc_haar (hθ : 0 < θ) :
    Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) ((muNB D θ).map (conjE (Formalism.L2.SG.Pf.muT_ne D))) :=
  haarN_tor (Formalism.L2.SG.Pf.muT_ne D)
    (Formalism.MainNotions.BridgeCSB.haarLieN _ _ _ (Formalism.L2.SG.Pf.Choice.kapN_ne_zero D hθ) ENNReal.ofReal_ne_top)

theorem hty_c (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    IsHCTypeW D.R.k D.R.rS (zB X (C.Qi τ) u τ) (fun i => ((D.hcW u τ).u i : ℝ)) (piB X (Qcs C τ) (Qics C τ) u τ) := by
  have h := Formalism.L2.SG.Pf.Choice.colsTypeTr_of X (Formalism.L2.SG.Pf.cfS_ne D) (transpC' C τ) u
  rw [zc_eq] at h
  rw [show X.pl (vOf X τ) = τ from X.pl.apply_symm_apply τ] at h
  exact h

theorem zT (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.inWb D.R.k D.R.rS (zB X (C.Qi τ) u τ) ∧ 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by
  refine ⟨(Formalism.L2.SG.Pf.zTr C u τ).1, ?_⟩
  rw [(Formalism.L2.SG.Pf.zTr C u τ).2]
  exact Formalism.L2.SG.Pf.Choice.Tr_pos D u

def Dc (C : Choice X θ) (hθ : 0 < θ) (u u' : D.what₂.Word) (τ : D.what₂.Tau) :
    Formalism.FourierDecayAlt.B.RealPlaceData D.R.k D.R.rS (X.Vloc u (vOf X τ)) (X.Vloc u' (vOf X τ)) where
  z := zB X (C.Qi τ) u τ
  z' := zB X (C.Qi τ) u' τ
  π := piB X (Qcs C τ) (Qics C τ) u τ
  π' := piB X (Qcs C τ) (Qics C τ) u' τ
  μG := muGB X (Qcs C τ) (Qics C τ) τ
  μW := C.muW u τ
  μN := (muNB D θ).map (conjE (Formalism.L2.SG.Pf.muT_ne D))
  μW' := C.muW u' τ
  μsec := (Formalism.L2.SG.Pf.BaseOf.sec_exists (Formalism.L2.SG.Pf.BaseOf.k_pos D) _ _ (zT C u τ).2 (zT C u' τ).2
    (let ⟨g, hg, _⟩ := hty_c C u τ; ⟨g, hg⟩) (let ⟨g, hg, _⟩ := hty_c C u' τ; ⟨g, hg⟩)).choose
  χ := Formalism.FourierDecayAlt.P.character_exists_alt.choose
  k_pos := Formalism.L2.SG.Pf.BaseOf.k_pos D
  z_mem := (zT C u τ).1
  z'_mem := (zT C u' τ).1
  T_pos := (zT C u τ).2
  T'_pos := (zT C u' τ).2
  π_rep := (Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved _ _ _ _ _ _ (zT C u τ).1 (zT C u τ).2 (hty_c C u τ)).1
  π'_rep := (Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved _ _ _ _ _ _ (zT C u' τ).1 (zT C u' τ).2 (hty_c C u' τ)).1
  π_unitary := (Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved _ _ _ _ _ _ (zT C u τ).1 (zT C u τ).2 (hty_c C u τ)).2.1
  π'_unitary := (Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved _ _ _ _ _ _ (zT C u' τ).1 (zT C u' τ).2 (hty_c C u' τ)).2.1
  π_cont := (Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved _ _ _ _ _ _ (zT C u τ).1 (zT C u τ).2 (hty_c C u τ)).2.2
  π'_cont := (Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved _ _ _ _ _ _ (zT C u' τ).1 (zT C u' τ).2 (hty_c C u' τ)).2.2
  haarG := Formalism.L2.SG.Pf.BaseOf.haarG_B (n_eq' X) (X.B.I.ε (vOf X τ)) (transpC' C τ).2.1 (transpC' C τ).2.2.1
  haarW := Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.1 _ _ _ _ (zT C u τ).1 (zT C u τ).2 (C.muW_haar u τ)
  haarN := Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 _ _ _ (muNc_haar hθ)
  haarW' := Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.1 _ _ _ _ (zT C u' τ).1 (zT C u' τ).2 (C.muW_haar u' τ)
  sec := (Formalism.L2.SG.Pf.BaseOf.sec_exists (Formalism.L2.SG.Pf.BaseOf.k_pos D) _ _ (zT C u τ).2 (zT C u' τ).2
    (let ⟨g, hg, _⟩ := hty_c C u τ; ⟨g, hg⟩) (let ⟨g, hg, _⟩ := hty_c C u' τ; ⟨g, hg⟩)).choose_spec
  χ_smooth := Formalism.FourierDecayAlt.P.character_exists_alt.choose_spec.1
  χ_supp := Formalism.FourierDecayAlt.P.character_exists_alt.choose_spec.2.1
  χ_int := Formalism.FourierDecayAlt.P.character_exists_alt.choose_spec.2.2

theorem sideC (C : Choice X θ) (hθ : 0 < θ) (u : D.what₂.Word) (τ : D.what₂.Tau) {h : ℝ}
    (hgap : Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamD D τ) h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h)
    {w0 : X.B.H (vOf X τ)} (hlow : IsLowUnitH D.R.k D.R.rS (epsSH D.R) (lamD D τ) (sigB X (Qcs C τ) (Qics C τ) τ) w0) :
    ∃ νq, Formalism.FourierDecayAlt.ThreeDimData.Side D.R.k D.R.rS (epsSH D.R) (lamD D τ) h (sigB X (Qcs C τ) (Qics C τ) τ) w0
      (zB X (C.Qi τ) u τ) Formalism.QuantumDeterminants.cStd (fun i => ((D.hcW u τ).u i : ℝ)) (piB X (Qcs C τ) (Qics C τ) u τ)
      (C.muW u τ) ((muNB D θ).map (conjE (Formalism.L2.SG.Pf.muT_ne D))) (muGB X (Qcs C τ) (Qics C τ) τ) νq := by
  obtain ⟨hz, hT⟩ := zT C u τ
  have h2 := (transpC' C τ).2.1
  have hg := (transpC' C τ).2.2.1
  have hDS : IsDSHpk D.R.k D.R.rS (epsSH D.R) (lamD D τ) (sigB X (Qcs C τ) (Qics C τ) τ) := by
    obtain ⟨P, hP⟩ := Formalism.MainNotions.S.Inh.obj_cayleyU_rows D
    refine ⟨P, hP, ?_⟩
    exact dsHpk_tr (n_eq' X) (X.B.I.ε (vOf X τ)) (epsSH D.R)
      (fun i => by rw [X.eps_eq]; exact congrArg (epsS D.R) (Fin.ext rfl))
      (X.B.lam (vOf X τ)) (lamD D τ)
      (fun i => by
        rw [X.lam_eq, show X.pl (vOf X τ) = τ from X.pl.apply_symm_apply τ]
        exact congrArg (lamS D.R (D.hc τ)) (Fin.ext rfl))
      (X.B.σ (vOf X τ)) (X.ds (vOf X τ)) (Qcs C τ) (Qics C τ) h2 hg P hP
  have hμG := haar_tr (n_eq' X) (X.B.I.ε (vOf X τ)) (Qcs C τ) (Qics C τ) h2 hg
  have hμN := muNc_haar (D := D) hθ
  obtain ⟨νq, hq⟩ := Formalism.L2.SG.Pf.QuotMeasExists.quotMeasExists _ _ _ hz hT _ _ hμG
    (isHaarOn_muS_gen hz hT (C.muW_haar u τ) (C.muW_one u τ) (Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 _ _ _ hμN))
  exact ⟨νq, Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D τ, hDS, hgap, hok, hlow, hz, hT, cStd_ne, hty_c C u τ,
    C.muW_haar u τ, hμN, hμG, hq⟩

end Formalism.L2.SG.RealObj.EnergyIntLoc
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.NormCut

theorem colFreeAll (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u : D.what₂.Word) :
    ColFree (X.Fu u) Y.TR (Y.cs u) (Aset Y.TR (Y.cs u)) (scOf Y.TR (Y.cs u)) :=
  colFree_steps Y.TR (Y.cs u) Y.hK (Y.colReps u) (Formalism.L2.SG.Closed.NeatKu_holds X u Y.hK)
    (Formalism.L2.SG.Pf.NormSteps.levi_onto_reduction Y.TR (Y.cs u))
    (Formalism.L2.SG.Pf.NormSteps.column_lattice_representatives (Y.cs u) Y.hK (Y.rowsOK u)) (Formalism.L2.SG.Pf.massAC_holds D X Y u)

theorem leftActC'_of_PD (hPD : ∀ D : D7, Formalism.L2.SG.Saturated.PDIso D) : Formalism.L2.SG.Pf.SatGramActL.LeftActC' := by
  have hB : Formalism.L2.SG.Pf.SatGramActL.ChiNBiAll := by
    first
    | exact fun D X => chi_n_bilinear X
    | (intro D X; exact chi_n_bilinear X)
  have hGen : ∀ D : D7, Formalism.L2.SG.Saturated.GenIso (VS D) D.R.rS (gS D) := by
    intro D
    first
    | exact Formalism.L2.SG.Pf.generic_isomorphism_holds (gS D)
    | exact Formalism.L2.SG.Pf.generic_isomorphism_holds _
    | exact Formalism.L2.SG.Pf.generic_isomorphism_holds _ _ _
  exact Formalism.L2.SG.Pf.SatGramActL.left_action_of_local_data hPD hGen Formalism.L2.SG.Pf.iotaRepC_holds
    Formalism.L2.SG.Pf.ampRepNC_holds hB

theorem rightActC'_holds : Formalism.L2.SG.Pf.SatGramActR.RightActC' := by
  have hB : Formalism.L2.SG.Pf.SatGramActL.ChiNBiAll := by
    first
    | exact fun D X => chi_n_bilinear X
    | (intro D X; exact chi_n_bilinear X)
  exact Formalism.L2.SG.Pf.SatGramActR.right_action_three_families hB Formalism.L2.SG.Pf.iotaRepC_holds Formalism.L2.SG.Pf.ampRepNC_holds

theorem normExpSatC'_of_PD (hPD : ∀ D : D7, Formalism.L2.SG.Saturated.PDIso D) : NormExpSatC' := by
  have hN : NeatC := Formalism.L2.SG.Closed.NeatC_holds
  exact normExpSatC'_of_acts hN Formalism.L2.SG.Pf.massAC_holds (leftActC'_of_PD hPD) rightActC'_holds

theorem degLeftAct_of_PD (hPD : ∀ D : D7, Formalism.L2.SG.Saturated.PDIso D) (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (Y : Full X) (u : D.what₂.Word) (h1 : OOIntAll X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u))
    (h2 : AmpWellDef (X.Fu u) (X.Fu u) (Y.cs u) (Y.cs u)) (h3 : OOFundIndep X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u)) :
    Formalism.L2.SG.Pf.SatGram.LeftAct (X.Fu u) (X.Fu u) Y.TR (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) (Y.tO u u).degSet
      (Aset Y.TR (Y.cs u)) :=
  leftActC'_of_PD hPD D X Y u u h1 h2 h3 _ (by simp)

theorem degRightAct_holds (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u : D.what₂.Word)
    (h1 : OOIntAll X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u))
    (h2 : AmpWellDef (X.Fu u) (X.Fu u) (Y.cs u) (Y.cs u)) (h3 : OOFundIndep X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u)) :
    Formalism.L2.SG.Pf.SatGram.RightAct (X.Fu u) (X.Fu u) Y.TR (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) (Y.tO u u).degSet
      (Aset Y.TR (Y.cs u)) :=
  rightActC'_holds D X Y u u h1 h2 h3 _ (by simp)

end Formalism.L2.SG.NormCut
end
end

section

noncomputable section

open MeasureTheory Topology NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SetM

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def eV (v : InfinitePlace X.B.I.F) : Fin D.R.rS → Fin X.B.I.n → ℂ := fun a => rv X.B.I v (X.eR a)
def pV (v : InfinitePlace X.B.I.F) : Fin D.R.rS → Fin X.B.I.n → ℂ := fun a => rv X.B.I v (X.fR a)
def zV (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : Fin X.B.I.n → ℂ := rv X.B.I v (X.zR u)

def NGv (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : Subgroup (Formalism.REAL.UJ (X.B.I.ε v)) :=
  NilradicalHermitianFrames.NH.NG (X.B.I.ε v) (eV X v) (zV X u v)
def HGv (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : Subgroup (Formalism.REAL.UJ (X.B.I.ε v)) :=
  NilradicalHermitianFrames.NH.HG (X.B.I.ε v) (eV X v) (pV X v) (zV X u v)
def muNv (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : Measure (Formalism.REAL.UJ (X.B.I.ε v)) :=
  haarSub (NGv X u v) (NilradicalHermitianFrames.NH.NG_closed _ _ _)
def muHv (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : Measure (Formalism.REAL.UJ (X.B.I.ε v)) :=
  haarSub (HGv X u v) (NilradicalHermitianFrames.NH.HG_closed _ _ _ _)

def muSv (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : Measure (Formalism.REAL.UJ (X.B.I.ε v)) :=
  ((muNv X u v).prod (muHv X u v)).map (fun q => q.1 * q.2)

theorem muNv_haar (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    IsHaarS (NLoc (X.B.I.ε v) (eV X v) (zV X u v)) (muNv X u v) :=
  haarSub_isHaarS _ _
theorem muHv_haar (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    IsHaarS (HLoc (X.B.I.ε v) (eV X v) (pV X v) (zV X u v)) (muHv X u v) :=
  haarSub_isHaarS _ _

instance (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : SigmaFinite (muNv X u v) := (muNv_haar X u v).1.1
instance (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : SigmaFinite (muHv X u v) := (muHv_haar X u v).1.1

def NinfG (u : D.what₂.Word) : Subgroup X.B.I.Ginf := Subgroup.pi Set.univ (fun v => NGv X u v)
def HinfG (u : D.what₂.Word) : Subgroup X.B.I.Ginf := Subgroup.pi Set.univ (fun v => HGv X u v)

theorem NinfG_coe (u : D.what₂.Word) : (NinfG X u : Set X.B.I.Ginf) =
    Ninf X.B.I (fun a => crdOf X.B.I X.ιE X.bas (X.eX a)) (crdOf X.B.I X.ιE X.bas (X.zu u)) := by
  ext g
  unfold Ninf
  simp only [Set.mem_setOf_eq]
  show (∀ v ∈ (Set.univ : Set (InfinitePlace X.B.I.F)), g v ∈ NGv X u v) ↔ _
  simp only [Set.mem_univ, true_implies]
  exact Iff.rfl

theorem HinfG_coe (u : D.what₂.Word) : (HinfG X u : Set X.B.I.Ginf) =
    Hset X.B.I (Set.range (fun a => crdOf X.B.I X.ιE X.bas (X.eX a)) ∪
      Set.range (fun a => crdOf X.B.I X.ιE X.bas (X.fY a)) ∪ {crdOf X.B.I X.ιE X.bas (X.zu u)}) := by
  ext g
  unfold Hset
  simp only [Set.mem_setOf_eq]
  show (∀ v ∈ (Set.univ : Set (InfinitePlace X.B.I.F)), g v ∈ HGv X u v) ↔ _
  simp only [Set.mem_univ, true_implies]
  refine forall_congr' fun v => ?_
  constructor
  · rintro ⟨he, hp, hz⟩ x hx
    rcases hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hx
    · exact he a
    · exact hp a
    · rw [Set.mem_singleton_iff.1 hx]
      exact hz
  · intro h
    exact ⟨fun a => h _ (Or.inl (Or.inl ⟨a, rfl⟩)), fun a => h _ (Or.inl (Or.inr ⟨a, rfl⟩)), h _ (Or.inr rfl)⟩

theorem NinfG_closed (u : D.what₂.Word) : IsClosed (NinfG X u : Set X.B.I.Ginf) := by
  show IsClosed (Set.univ.pi fun v => (NGv X u v : Set (Formalism.REAL.UJ (X.B.I.ε v))))
  exact isClosed_set_pi fun v _ => NilradicalHermitianFrames.NH.NG_closed _ _ _

theorem HinfG_closed (u : D.what₂.Word) : IsClosed (HinfG X u : Set X.B.I.Ginf) := by
  show IsClosed (Set.univ.pi fun v => (HGv X u v : Set (Formalism.REAL.UJ (X.B.I.ε v))))
  exact isClosed_set_pi fun v _ => NilradicalHermitianFrames.NH.HG_closed _ _ _ _

theorem muN_eq (u : D.what₂.Word) : ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ X.muN u = κ • Measure.pi (muNv X u) := by
  obtain ⟨hσ, h0, hc, hi⟩ := X.muN_haar u
  haveI := hσ
  have hv : ∀ v, IsHaarS (NGv X u v : Set (Formalism.REAL.UJ (X.B.I.ε v))) (muNv X u v) :=
    fun v => haarSub_isHaarS _ _
  have hc' : X.muN u (NinfG X u : Set X.B.I.Ginf)ᶜ = 0 := by rw [NinfG_coe]; exact hc
  have hi' : ∀ h ∈ NinfG X u, (X.muN u).map (fun x => h * x) = X.muN u := by
    intro h hh
    apply hi
    rw [← NinfG_coe]
    exact hh
  refine PiM.uniq_on_closed (NinfG X u) (NinfG_closed X u) (X.muN u) (Measure.pi (muNv X u)) hc' ?_ hi' ?_ h0
    (PiM.pi_ne_zero _ fun v => (hv v).1.2.1)
  · show Measure.pi (muNv X u) (Set.univ.pi fun v => (NGv X u v : Set (Formalism.REAL.UJ (X.B.I.ε v))))ᶜ = 0
    exact PiM.pi_conc _ _ fun v => (hv v).1.2.2.1
  · intro g hg
    exact PiM.pi_map_mul_left _ g fun v => (hv v).1.2.2.2 (g v) ((Subgroup.mem_pi _).mp hg v (Set.mem_univ v))

theorem muH_eq (u : D.what₂.Word) : ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ X.muH u = κ • Measure.pi (muHv X u) := by
  obtain ⟨hσ, h0, hc, hi⟩ := X.muH_haar u
  haveI := hσ
  have hv : ∀ v, IsHaarS (HGv X u v : Set (Formalism.REAL.UJ (X.B.I.ε v))) (muHv X u v) :=
    fun v => haarSub_isHaarS _ _
  have hc' : X.muH u (HinfG X u : Set X.B.I.Ginf)ᶜ = 0 := by rw [HinfG_coe]; exact hc
  have hi' : ∀ h ∈ HinfG X u, (X.muH u).map (fun x => h * x) = X.muH u := by
    intro h hh
    apply hi
    rw [← HinfG_coe]
    exact hh
  refine PiM.uniq_on_closed (HinfG X u) (HinfG_closed X u) (X.muH u) (Measure.pi (muHv X u)) hc' ?_ hi' ?_ h0
    (PiM.pi_ne_zero _ fun v => (hv v).1.2.1)
  · show Measure.pi (muHv X u) (Set.univ.pi fun v => (HGv X u v : Set (Formalism.REAL.UJ (X.B.I.ε v))))ᶜ = 0
    exact PiM.pi_conc _ _ fun v => (hv v).1.2.2.1
  · intro g hg
    exact PiM.pi_map_mul_left _ g fun v => (hv v).1.2.2.2 (g v) ((Subgroup.mem_pi _).mp hg v (Set.mem_univ v))

theorem muS_eq (u : D.what₂.Word) (hσ : ∀ v, SigmaFinite (muSv X u v)) :
    ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ muS X u = κ • Measure.pi (muSv X u) := by
  obtain ⟨κ1, h1, h1', hN⟩ := muN_eq X u
  obtain ⟨κ2, h2, h2', hH⟩ := muH_eq X u
  have key : ((Measure.pi (muNv X u)).prod (Measure.pi (muHv X u))).map (fun p => p.1 * p.2) =
      Measure.pi (muSv X u) := by
    rw [← (measurePreserving_piProd (muNv X u) (muHv X u)).map_eq,
      Measure.map_map (g := fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2)
        (show Measurable (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) from
          (continuous_fst.mul continuous_snd).measurable) piProdEquiv.measurable]
    exact Measure.pi_map_pi
      (f := fun v (q : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v)) => q.1 * q.2) (hμ := hσ)
      (fun v => (show Measurable (fun q : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => q.1 * q.2) from
        (continuous_fst.mul continuous_snd).measurable).aemeasurable)
  refine ⟨κ1 * κ2, mul_ne_zero h1 h2, ENNReal.mul_ne_top h1' h2', ?_⟩
  show ((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2) = _
  rw [hN, hH, Measure.prod_smul_left, Measure.prod_smul_right, Measure.map_smul, Measure.map_smul, key,
    smul_smul]
  all_goals exact (show Measurable (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) from
    (continuous_fst.mul continuous_snd).measurable).aemeasurable

end SetM

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
end
end
