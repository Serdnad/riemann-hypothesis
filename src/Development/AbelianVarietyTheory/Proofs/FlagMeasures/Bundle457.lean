module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle013
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeBoundAtTermsOfLocalData
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle016
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsCnt
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle004
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle338
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle422
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle401
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle456
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

@[expose] public section

section


theorem _root_.GlobalTheory.T.amplitudeBound_at_terms_of_localData : GlobalTheory.TypeAsm.LocDatC → GlobalTheory.TypeAsm.TailP → GlobalTheory.TypeAsm.AmpP := by
  first | exact @GlobalTheory.TypeAsm.AmpTerms.amplitudeBound_of_localData_of_tailBound | exact GlobalTheory.TypeAsm.AmpTerms.amplitudeBound_of_localData_of_tailBound | (intros; apply GlobalTheory.TypeAsm.AmpTerms.amplitudeBound_of_localData_of_tailBound <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.MainNotions.BridgeLemma₂ Formalism.L2.SG.RowsU

theorem _root_.GlobalTheory.T.loopRowBounds_along_family_largeGaps : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 A C1 cV CGam : ℝ, ∃ C₀ thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), Fm.CGam = CGam → thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → (OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) ∧ ∀ (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)) (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1), rows_TiesF Fm C1 X Y → (∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), wordPairTermInjective (X x hx i) (Y x hx i u u')) → (∀ x (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), wordPairBetaLattice (Fm.D x i) u u') → (OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u', VanishingOnXAndXPlus.TermVolumeSmallCellBound (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1 (Y x hx i u u') C' Cl Cg cb Cu cT CT C0 A cV) → ∀ C ≥ C₀, OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u', Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A → RowsND (X x hx i) (Y x hx i u u') C ∧ RowsDeg (X x hx i) (Y x hx i u u') C ∧ RowsOne (X x hx i) (Y x hx i u u') C := by
  first | exact @GlobalTheory.LoopRowBoundsGap.rows_along_family | exact GlobalTheory.LoopRowBoundsGap.rows_along_family | (intros; apply GlobalTheory.LoopRowBoundsGap.rows_along_family <;> assumption)
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  Formalism.L2.SG.FamDefs Formalism.MainNotions.S.LocNG

namespace GlobalTheory.SnFam

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem setQ_locClosed {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (S : Prop → Prop)
    (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (w : Point D.host.E (D.R.rS + 1)) (hw : ZhatOM (ZhatL F F') = ptMat w) (hG : Gval F F' ≠ 0)
    (FP : ∀ p : PlF D, LocNG.FPair (locH (zOf Y) p) D.R.rS)
    (hB : GlobalTheory.Unfold.Based (zOf Y) FP (Tu D u) (Tu D u') F F') :
    GlobalTheory.Unfold.LocClosed F F' (zOf Y) FP (setQ Y u u' S) := by
  have hRel : ∀ p, (FP p).RelG (LocNG.theta ((zOf Y).M p)) := fun p =>
    (GlobalTheory.T.localisedBaseFrames_relevantPair D (zOf Y) u u' w F F' hw hG p).2 (FP p) (hB p)
  obtain ⟨hng, hgen, -, -⟩ := GlobalTheory.T.nonGeneric_generic_terms_closed_under_localUnitary D X Y u u' F F' w hw hG (zOf Y) FP hB hRel
  intro t t' Λ Λ' hΛ hΛ' hloc ht
  have hGt : ∀ s : TauC Y u u', s.G ≠ 0 → (Y.tO u u').G s ≠ 0 := fun s hs => by
    show Formalism.L2.SG.TermOp.Gt s ≠ 0
    simp [Formalism.L2.SG.TermOp.Gt, hs]
  have h1 := hGt t (GlobalTheory.T.term_at_base_point_of_frames D X Y u u' F F' w hw hG t Λ hΛ).1
  have h2 := hGt t' (GlobalTheory.T.term_at_base_point_of_frames D X Y u u' F F' w hw hG t' Λ' hΛ').1
  have hiff : (Y.tO u u').gener t ↔ (Y.tO u u').gener t' := by
    constructor
    · intro hg
      exact (hgen t t' Λ Λ' hΛ hΛ' hloc ⟨h1, hg⟩).2
    · intro hg'
      by_contra hg
      exact (hng t t' Λ Λ' hΛ hΛ' hloc ⟨h1, hg⟩).2 hg'
  have he : (¬ (Y.tO u u').gener t) = (¬ (Y.tO u u').gener t') := propext (not_congr hiff)
  exact ⟨h2, he ▸ ht.2⟩

theorem familyRowWeightSumUnfoldingIdentity_proof : FamilyWeightSumUnfoldingIdentity := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, ?_⟩
  intro C' Cl _ _ D large₂ X Y u u' _ K S TS cls hF γ _ Fm hT
  obtain ⟨hTS, hCR, -⟩ := hF
  subst hTS
  exact GlobalTheory.T.unfolding_identity_matched_family_closed_terms D X Y u u' _ cls hCR
    (fun F F' w hw hG FP hB => setQ_locClosed Y u u' S F F' w hw hG FP hB) γ Fm hT

end GlobalTheory.SnFam
end
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localBesselJFactor_all_words_of_gap : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (C : Choice X 1) (hB : WuBessel C) (u u' : D.what₂.Word), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → JFactN hI C hB u u' := by
  first | exact @GlobalTheory.JFactTie.jFactN_all | exact GlobalTheory.JFactTie.jFactN_all | (intros; apply GlobalTheory.JFactTie.jFactN_all <;> assumption)
end
