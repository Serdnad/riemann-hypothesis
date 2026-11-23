module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle332
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle328
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle224
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle444
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle429
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FormAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelCharPfRat
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpFibreConstOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinGlob
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BaseOfCore
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.LintegralFintypeProd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.WeilQuotientGlobalAssumptions
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilFormulaBesselNormSqBruhatProduct
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinLoc

@[expose] public section

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AmpLift.amp_lift : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (θ : ℝ) (C : Choice X θ) (u u' : D.what₂.Word) (s : TT Y u u') (x : Point D.host.E (D.R.rS + 1) × Measure X.B.I.Ginf × Set X.B.I.Ginf), s.relevant → s.G ≠ 0 → s.toTerm.atPt x.1 → Formalism.L2.SG.VolPin.IsPinnedR s x.1 x.2.1 → IsFundR s x.2.2 → (∀ v, ∀ r ∈ Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (s.pt.1 v), ∀ y, Formalism.L2.SG.TermOp.rk1 (X.Wloc u v (r * y)) (X.Wloc u' v ((s.pt.1 v)⁻¹ * (r * y))) = Formalism.L2.SG.TermOp.rk1 (X.Wloc u v y) (X.Wloc u' v ((s.pt.1 v)⁻¹ * y))) → ∃ μl νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)), (∀ v, Formalism.L2.SG.RealObj.IsHaarLoc (Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (s.pt.1 v)) (μl v)) ∧ (∀ v, Formalism.L2.SG.RealObj.IsQuotLoc (μl v) (νl v)) ∧ (∀ τ, ∃ p, IsRootMeasR D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) p (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) ((μl (vOf X τ)).map (fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) ((s.pt.1 (vOf X τ))⁻¹ * y * (s.pt.1 (vOf X τ))))))) ∧ hsNormSq (Formalism.L2.SG.TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') s) = (Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2) ^ 2 * (x.2.1 x.2.2).toReal ^ 2 * ∏ v, hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v); Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u' v) (s.pt.1 v)) := by
  intro D X Y θ C u u' s x hrel _hG _hat hpin hfund hinv
  obtain ⟨μl, hμeq, hHaar, hHR, hroot⟩ := GlobalTheory.T.normalisedMeasure_eq_prod_besselRootMeasures D X Y θ C u u' s x.1 x.2.1 hpin
  obtain ⟨hq, ν, hν⟩ := GlobalTheory.T.exists_quotient_measure_unipotent_stabilisers D X u u' s.pt.1 μl hHaar
  choose νl hνl using hq
  refine ⟨μl, νl, hHaar, hνl, hroot, ?_⟩
  have hν' : IsQuotMeasS X.B.I x.2.1 ν := hμeq ▸ hν
  have hOO := Formalism.L2.SG.Pf.formAllC_holds D X Y u u' s x.2.1 ν x.2.2
    (Formalism.L2.SG.Pf.RelChar.relCharC_holds D X Y u u' s hrel) hHR hν' hfund.1 hfund.2
  have hprod := GlobalTheory.T.realOrbitalIntegral_hsNorm_eq_prod_local D X u u' s.pt.1 μl νl ν hHaar hνl hν hinv
  unfold Formalism.L2.SG.TermOp.ampN
  rw [Formalism.L2.SG.LoopTerm.hsNormSq_smul, Formalism.L2.SG.LoopTerm.hsNormSq_smul, hOO,
    ← Complex.coe_smul, Formalism.L2.SG.LoopTerm.hsNormSq_smul, hprod]
  have hc : Complex.normSq (Formalism.L2.SG.TermOp.chiN X (Formalism.L2.SG.TermOp.kOf X u u' ((Y.cs u).h ((Y.cs u).base s.lam) : X.B.I.Gf) ((Y.cs u').h ((Y.cs u').base s.lam') : X.B.I.Gf) s.pt)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Formalism.L2.SG.Pf.FibreCounting.norm_chiN, one_pow]
  rw [hc, Complex.normSq_ofReal, Complex.normSq_ofReal]
  ring
end

section

noncomputable section

namespace GlobalTheory.LoopVol

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hhz_dcrel {D : D7} (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS T') (h : Formalism.L2.SG.TermDef.DCRel Λ F F₁ F₂) (b C : ℝ) :
    Formalism.MainNotions.S.Cnt.HHZ D b C (ZhatL F F₂) = Formalism.MainNotions.S.Cnt.HHZ D b C (ZhatL F F₁) := by

  have hm : ∀ l : ℕ, leadMinorE (ZhatL F F₂) l = leadMinorE (ZhatL F F₁) l :=
    GlobalTheory.T.leadMinor_gramMatrix_const_doubleCoset D Λ T T' F F₁ F₂ h
  simp only [Formalism.MainNotions.S.Cnt.HHZ, Formalism.MainNotions.S.Cnt.sizeZ, Formalism.MainNotions.S.Cnt.absDl, hm]

theorem volRC_le : ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C : ℝ, ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (W : WittDat X) (H : TieHyp W hI) (Am : AmpDat X) (hV : PvalForm W hI Am) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), 1 ≤ Cl → Formalism.MainNotions.S.Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t → Formalism.L2.SG.LoopTerm.volRC hI t ≤ Formalism.MainNotions.S.Cnt.HHZ D large₂.sc.b C (ZhatL ((termTieOf W hI H Am hV).fl t) ((termTieOf W hI H Am hV).fl' t)) ^ (C * (D.R.rS : ℝ) ^ 2) := by
  intro Cg cb Cu cT CT C0 A
  obtain ⟨C, hC1, hcov⟩ := GlobalTheory.T.covolume_integralUnipotentStabilizer_of_term Cg cb Cu cT CT C0 A
  refine ⟨C, ?_⟩
  intro D X Y hF hI W H Am hV large₂ u u' C' Cl hCl hHyp t hG hrel

  have hexp : (0 : ℝ) ≤ C * (D.R.rS : ℝ) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hone : ∀ Z : Formalism.MainNotions.S.Cnt.GramM D,
      (1 : ℝ) ≤ Formalism.MainNotions.S.Cnt.HHZ D large₂.sc.b C Z ^ (C * (D.R.rS : ℝ) ^ 2) := fun Z =>
    Real.one_le_rpow (Formalism.MainNotions.BridgeLemma₂.rows_one_le_HHZ D large₂ (by linarith) Z) hexp
  show Formalism.L2.SG.LoopTerm.volRC hI t ≤ Formalism.MainNotions.S.Cnt.HHZ D large₂.sc.b C
    (ZhatL (lf D (FlagOfWord W u)) (fl'Of W hI t)) ^ (C * (D.R.rS : ℝ) ^ 2)
  unfold Formalism.L2.SG.LoopTerm.volRC
  split_ifs with h
  swap
  · exact hone _
  have hs : h.2.2.choose.toTerm = tc hI t := h.2.2.choose_spec
  generalize h.2.2.choose = s at hs ⊢
  unfold Formalism.L2.SG.LoopTerm.covR
  split_ifs with hp
  swap
  · exact hone _
  have hat : s.toTerm.atPt hp.choose.1 := hp.choose_spec.1
  have hpin : Formalism.L2.SG.VolPin.IsPinnedR s hp.choose.1 hp.choose.2.1 := hp.choose_spec.2.1
  have hfund : Formalism.L2.SG.LoopTerm.IsFundR s hp.choose.2.2 := hp.choose_spec.2.2
  generalize hp.choose = x at hat hpin hfund ⊢
  obtain ⟨w, μR, K⟩ := x
  dsimp only at hat hpin hfund ⊢

  have htrel : (tc hI t).relevant := (hI.relevant t).1 hrel
  have hsrel : s.relevant := by
    show s.toTerm.relevant
    rw [hs]; exact htrel
  have hsG : s.G ≠ 0 := by
    show s.toTerm.G ≠ 0
    rw [hs, ← gterm_val hI t]
    exact (map_ne_zero _).2 hG

  have hP0 : Formalism.L2.SG.TermDef.PD D s.lam (lf D (X.Fu u)) u' s.frame := s.rep.2.2.2.2
  have hcls : s.toTerm.cls = Formalism.L2.SG.TermDef.mk _ _ _ ⟨s.frame, hP0⟩ := rfl
  have hEq := Formalism.L2.SG.TermTieOf.eqIff_base (Y := Y) (u' := u') s.lam s.mem
  obtain ⟨F₁, ⟨hP₁, hmk₁⟩, hG₁, hc₁⟩ := id hat
  have hR₁ : Formalism.L2.SG.TermDef.Rel s.lam (lf D (X.Fu u)) (Formalism.L2.SG.TermDef.PD D s.lam (lf D (X.Fu u)) u')
      ⟨F₁, hP₁⟩ ⟨s.frame, hP0⟩ := (hEq _ _).1 (hmk₁.trans hcls)
  have hcb := (Formalism.L2.SG.TermTieOf.cellQ s.toTerm w ⟨F₁, hP₁⟩ ⟨s.frame, hP0⟩ hR₁).1 ⟨hG₁, hc₁⟩

  have hlf := Formalism.L2.SG.TermTieOf.mapL_lf W u
  have hZ : ZhatL (lf D (FlagOfWord W u)) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) =
      ZhatL (lf D (X.Fu u)) s.frame := by
    rw [← hlf]; exact Formalism.L2.SG.Saturated.zhat_mapL _ _ _ _
  have hGv : Gval (lf D (FlagOfWord W u)) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) ≠ 0 := by
    rw [← hlf]
    exact (Formalism.L2.SG.Saturated.gval_mapL (W.δ u) (W.isom u) (lf D (X.Fu u)) s.frame).trans_ne hcb.1
  have hcell : IsInCell (ZhatOM (ZhatL (lf D (FlagOfWord W u))
      (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame))) w := by
    rw [hZ]; exact hcb.2
  obtain ⟨L, U, hL, hU, hLU⟩ := hcell
  have hPm : Formalism.L2.SG.TermDef.PD D (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (lf D (FlagOfWord W u)) u'
      (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) := by
    rw [← hlf]
    exact (Formalism.L2.SG.Pf.positive_definite_isomorphism D u' (W.δ u) (W.isom u) s.lam (lf D (X.Fu u)) s.frame).2 hP0

  obtain ⟨Ω, hΩ, hvol, hcv⟩ := hcov D large₂ u u' C' Cl hCl hHyp (FlagOfWord W u) (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam)
    ⟨F0rec_e W u, F0rec_z_eq_zmOf W u⟩ (rowLat_rec H.lat s.lam s.mem)
    (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) ⟨⟨hPm.1, hPm.2.1, hGv⟩, hPm.2.2⟩ w L U hL hU hLU
  have hμ := GlobalTheory.T.stabiliserCovolume_le_rootCoordinateCover Cg cb Cu cT CT C0 A D X Y W large₂ u u' C' Cl hHyp s hsrel hsG w μR K hat hpin hfund
    L U hL hU hLU Ω hΩ hcv
  have hle := hμ.trans hvol

  have hout : Formalism.L2.SG.TermDef.DCRel s.lam (lf D (X.Fu u)) (Quot.out s.toTerm.cls).1 s.frame :=
    (hEq (Quot.out s.toTerm.cls) ⟨s.frame, hP0⟩).1 ((Quot.out_eq _).trans hcls)
  have hdc : Formalism.L2.SG.TermDef.DCRel (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (lf D (FlagOfWord W u))
      (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) (Quot.out s.toTerm.cls).1)
      (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) := by
    rw [← hlf]
    exact (Formalism.L2.SG.Pf.double_coset_isomorphism _ _ (W.δ u) (W.isom u) s.lam (lf D (X.Fu u)) _ _).2 hout
  have hfl : fl'Of W hI t = Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) (Quot.out s.toTerm.cls).1 := by
    rw [hs]; rfl
  rw [hfl, ← hhz_dcrel _ _ _ _ hdc large₂.sc.b C]
  exact ENNReal.toReal_le_of_le_ofReal (le_trans zero_le_one (hone _)) hle

end GlobalTheory.LoopVol

end
end

section

open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnitW

open Formalism.L2.SG.Pf.AmpWinLoc Formalism.L2.SG.Pf.Choice

theorem loc_at {D : D7} {X : HidaSetting D} (C : Choice X 1) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (v : InfinitePlace X.B.I.F) (hv : vOf X τ = v) :
    SigmaFinite (muNl C τ v) ∧ SigmaFinite (muHl C u τ v) ∧
    QPK.mulMap (muNl C τ v) (muHl C u τ v)
      (QPK.prodSet (Formalism.L2.SG.Pf.WuDec.Nloc X u v) (Formalism.L2.SG.Pf.WuDec.Hfix X u v))ᶜ = 0 ∧
    ∃ β : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞, Measurable β ∧
      (∀ x, ∫⁻ s, β (s * x) ∂(QPK.mulMap (muNl C τ v) (muHl C u τ v)) = 1) ∧
      ∫⁻ y, β y * ‖X.Wloc u v y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε v)) = l2SG (C.nuS u τ) (wT C u τ) := by
  subst hv
  obtain ⟨β, hβm, hβ1⟩ := bruhat_mulMap C u τ
  exact ⟨sf_muNl C τ one_pos, sf_muHl C u τ, (invOn_mulMap C u τ).2.2.1, β, hβm, hβ1, loc_id C u τ hβm hβ1⟩

theorem map_trI_H {D : D7} {X : HidaSetting D} (C : Choice X 1) (u : D.what₂.Word) :
    (Measure.pi (Formalism.L2.SG.Pf.AmpWinGlob.muHv C u)).map (trI C) = Measure.pi (C.muW u) := by
  have hPemb : MeasurableEmbedding
      (Pi.map (fun τ => eT C τ (X.pl.symm τ)) : (∀ τ : D.what₂.Tau, Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ))) → _) :=
    (Topology.IsClosedEmbedding.piMap fun τ =>
      Formalism.L2.SG.Pf.BaseOf.trG_closedEmb (n_eq' X) (X.B.I.ε (X.pl.symm τ)) (C.isT τ).2.1).measurableEmbedding
  have htr : trI C = (Pi.map (fun τ => eT C τ (X.pl.symm τ)) :
      (∀ τ : D.what₂.Tau, Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ))) → _) ∘
      (MeasurableEquiv.piCongrLeft (fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm).symm := by
    funext x τ
    rfl
  haveI : ∀ v, SigmaFinite (Formalism.L2.SG.Pf.AmpWinGlob.muHv C u v) := fun v => by
    have key : ∀ (τ : D.what₂.Tau) (w : InfinitePlace X.B.I.F), vOf X τ = w → SigmaFinite (muHl C u τ w) := by
      rintro τ w rfl; exact sf_muHl C u τ
    exact key (X.pl v) v (X.pl.symm_apply_apply v)
  rw [htr, ← Measure.map_map hPemb.measurable (MeasurableEquiv.measurable _)]
  have h1 : (Measure.pi (Formalism.L2.SG.Pf.AmpWinGlob.muHv C u)).map
      (MeasurableEquiv.piCongrLeft (fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm).symm =
      Measure.pi (fun τ => Formalism.L2.SG.Pf.AmpWinGlob.muHv C u (X.pl.symm τ)) :=
    ((measurePreserving_piCongrLeft (Formalism.L2.SG.Pf.AmpWinGlob.muHv C u) X.pl.symm).symm _).map_eq
  have h2 : (fun τ => Formalism.L2.SG.Pf.AmpWinGlob.muHv C u (X.pl.symm τ)) = fun τ => muHl C u τ (X.pl.symm τ) := by
    funext τ
    show muHl C u (X.pl (X.pl.symm τ)) (X.pl.symm τ) = muHl C u τ (X.pl.symm τ)
    rw [Equiv.apply_symm_apply]
  rw [h1, h2]
  have hmap : ∀ τ, (muHl C u τ (X.pl.symm τ)).map (eT C τ (X.pl.symm τ)) = C.muW u τ := fun τ => map_muHl C u τ
  have : ∀ τ, SigmaFinite ((muHl C u τ (X.pl.symm τ)).map (eT C τ (X.pl.symm τ))) := fun τ => by
    rw [hmap τ]; exact (C.muW_haar u τ).1
  refine (Measure.pi_map_pi (μ := fun τ => muHl C u τ (X.pl.symm τ)) (f := fun τ => eT C τ (X.pl.symm τ))
    (fun τ => (eT_emb C τ (X.pl.symm τ)).measurable.aemeasurable)).trans ?_
  simp_rw [hmap]

theorem prod_l2SG_eq : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (hB : WuBessel C), GoodLoc C hB →
    ∀ (u : D.what₂.Word) (cN cH : ℝ≥0∞), cN ≠ 0 → cN ≠ ⊤ → cH ≠ 0 → cH ≠ ⊤ →
    (∀ A : Set X.B.I.Ginf, MeasurableSet A → X.muN u A = cN * Measure.pi (fun _ : D.what₂.Tau => muNB D 1) (trI C '' A)) →
    (∀ A : Set X.B.I.Ginf, MeasurableSet A → X.muH u A = cH * Measure.pi (C.muW u) (trI C '' A)) →
    ∏ τ, l2SG (C.nuS u τ) (wT C u τ) = cN * cH := by
  intro D X C hB _ u cN cH hN0 hNt hH0 hHt hN hH
  have hv : ∀ v, vOf X (X.pl v) = v := fun v => X.pl.symm_apply_apply v
  have loc := fun v => loc_at C u (X.pl v) v (hv v)
  choose hsN hsH hconc β hβm hβ1 hβl using loc
  set μN : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)) := fun v => muNl C (X.pl v) v with hμN
  set μH : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)) := fun v => muHl C u (X.pl v) v with hμH
  haveI : ∀ v, SigmaFinite (μN v) := hsN
  haveI : ∀ v, SigmaFinite (μH v) := hsH
  haveI : SigmaFinite (muNB D 1) := (muNB_haar (D := D) one_pos).1
  haveI : ∀ τ, SigmaFinite (C.muW u τ) := fun τ => (C.muW_haar u τ).1
  obtain ⟨hemb0, hmapN⟩ := Formalism.L2.SG.Pf.AmpWinGlob.map_trInf C (fun v => hsN v) one_pos
  have hemb : MeasurableEmbedding (trI C) := hemb0
  have hmapH := map_trI_H C u
  have eN : X.muN u = cN • Measure.pi μN := by
    ext A hA
    have hc : Measure.pi (fun _ : D.what₂.Tau => muNB D 1) (trI C '' A) = Measure.pi μN A := by
      rw [← show (Measure.pi μN).map (trI C) = Measure.pi (fun _ : D.what₂.Tau => muNB D 1) from hmapN,
        hemb.map_apply, Set.preimage_image_eq _ hemb.injective]
    rw [hN A hA, hc, Measure.smul_apply, smul_eq_mul]
  have eH : X.muH u = cH • Measure.pi μH := by
    ext A hA
    have hc : Measure.pi (C.muW u) (trI C '' A) = Measure.pi μH A := by
      rw [← show (Measure.pi μH).map (trI C) = Measure.pi (C.muW u) from hmapH,
        hemb.map_apply, Set.preimage_image_eq _ hemb.injective]
    rw [hH A hA, hc, Measure.smul_apply, smul_eq_mul]
  set F : ∀ v, Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞ := fun v y => ‖X.Wloc u v y‖ₑ ^ 2 with hFdef
  have hFm : ∀ v, Measurable (F v) := fun v => (X.Wloc_cont u v).enorm.measurable.pow_const 2
  set f : X.B.I.Ginf → ℝ≥0∞ := fun x => ∏ v, β v (x v) * F v (x v) with hfdef
  have hfm : Measurable f :=
    Finset.measurable_prod _ fun v _ =>
      ((hβm v).comp (measurable_pi_apply v)).mul ((hFm v).comp (measurable_pi_apply v))
  have key := X.nuQ_weil u f hfm
  have hL1 : ∫⁻ x, f x ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) = ∏ τ, l2SG (C.nuS u τ) (wT C u τ) := by
    rw [hfdef, Formalism.L2.SG.ProjRows.muInf,
      QPK.lintegral_fintype_prod (fun v y => β v y * F v y) (fun v => (hβm v).mul (hFm v))]
    rw [← Fintype.prod_equiv X.pl (fun v => l2SG (C.nuS u (X.pl v)) (wT C u (X.pl v))) _ (fun v => rfl)]
    exact Finset.prod_congr rfl fun v _ => hβl v
  have hin : ∀ x, ∫⁻ s, f (s * x) ∂((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2) =
      (cN * cH) * ‖X.Wu u x‖ₑ ^ 2 := by
    intro x
    rw [lintegral_map (f := fun s => f (s * x))
      (show Measurable (fun s => f (s * x)) from hfm.comp (measurable_mul_const x)) measurable_mul,
      eN, eH, Measure.prod_smul_left, Measure.prod_smul_right, lintegral_smul_measure,
      lintegral_smul_measure]
    have h1 : ∀ p : X.B.I.Ginf × X.B.I.Ginf,
        f (p.1 * p.2 * x) = ∏ v, (fun v z => β v (z * x v) * F v (z * x v)) v (p.1 v * p.2 v) :=
      fun p => rfl
    simp_rw [h1]
    rw [QPK.lintegral_pi_prod_mul μN μH (fun v z => β v (z * x v) * F v (z * x v))
      (fun v => ((hβm v).comp (measurable_mul_const _)).mul ((hFm v).comp (measurable_mul_const _)))]
    have h2 : ∀ v, ∫⁻ s, β v (s * x v) * F v (s * x v) ∂(QPK.mulMap (μN v) (μH v)) = F v (x v) := by
      intro v
      have hae : ∀ᵐ s ∂(QPK.mulMap (μN v) (μH v)),
          s ∈ QPK.prodSet (Formalism.L2.SG.Pf.WuDec.Nloc X u v) (Formalism.L2.SG.Pf.WuDec.Hfix X u v) :=
        mem_ae_iff.mpr (hconc v)
      rw [lintegral_congr_ae (g := fun s => β v (s * x v) * F v (x v)) (hae.mono fun s hs => by
        obtain ⟨m, hm, h, hh, rfl⟩ := hs
        have hh' : h ∈ Formalism.L2.SG.Pf.WuDec.Hloc X u v := by rw [Formalism.L2.SG.Pf.WuDec.Hloc_eq]; exact hh
        have hs : m * h ∈ Formalism.L2.SG.Pf.WuDec.Sloc X u v :=
          Formalism.L2.SG.Pf.WuDec.mul_mem_Sloc X u _ (Formalism.L2.SG.Pf.WuDec.Nloc_sub X u _ hm)
            (Formalism.L2.SG.Pf.WuDec.Hloc_sub X u _ hh')
        show β v (m * h * x v) * ‖X.Wloc u v (m * h * x v)‖ₑ ^ 2 = β v (m * h * x v) * ‖X.Wloc u v (x v)‖ₑ ^ 2
        rw [← enorm_norm (X.Wloc u v (m * h * x v)), Formalism.L2.SG.Pf.WuDec.norm_Wloc_inv X u _ hs, enorm_norm])]
      rw [lintegral_mul_const _ (show Measurable (fun s => β v (s * x v)) from
        (hβm v).comp (measurable_mul_const _)), hβ1 v, one_mul]
    simp_rw [h2]
    have h3 : ∏ v, F v (x v) = ‖X.Wu u x‖ₑ ^ 2 := by
      rw [Formalism.L2.SG.Pf.WuDec.enorm_Wu X u x, Finset.prod_pow]
    rw [h3, smul_eq_mul, smul_eq_mul]
    ring
  simp_rw [hin] at key
  have hW1 : ∫⁻ x, ‖X.Wu u x‖ₑ ^ 2 ∂(X.nuQ u) = 1 := (X.Wu_spec u).2.2.2.2
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top hNt hHt), hW1, mul_one, hL1] at key
  exact key

end GlobalTheory.UnitW
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

theorem _root_.GlobalTheory.T.weil_formula_besselNormSq_bruhatProduct : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (κ : ℝ≥0∞) (M : ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))), (∀ v, SigmaFinite (M v)) → ((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2) = κ • Measure.pi M → ∀ (β : ∀ v : InfinitePlace X.B.I.F, Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞), (∀ v, Measurable (β v)) → (∀ v x, ∫⁻ s, β v (s * x) ∂(M v) = 1) → ∫⁻ x, (∏ v, β v (x v)) * ‖X.Wu u x‖ₑ ^ 2 ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) = κ := by
  first | exact @GlobalTheory.weil_bruhatProd_normSq | exact GlobalTheory.weil_bruhatProd_normSq | (intros; apply GlobalTheory.weil_bruhatProd_normSq <;> assumption)
end
