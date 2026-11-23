module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle058
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle045
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocFactorAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle014
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuBesselLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle004
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsCnt
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle004
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBGenIdx
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle022
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle007
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.Pf

theorem isLowUnitH_base_vector {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (τ : D.what₂.Tau) :
    IsLowUnitH D.R.k D.R.rS (epsSH D.R) (lamD D τ) (sigB X (C.Q τ) (C.Qi τ) τ) (v0Of C τ) := by
  obtain ⟨P, hP, hmem⟩ := C.y_low τ
  refine ⟨P, hP, ?_, hmem⟩
  obtain ⟨-, hiso⟩ := Formalism.L2.SG.Pf.WuBL.sigB_rep C τ
  show ‖X.B.σ (vOf X τ) (C.Q τ * C.y τ * C.Qi τ) (X.B.w (vOf X τ))‖ = 1
  rw [← (X.low (vOf X τ)).1]
  exact hiso (C.y τ) (C.y_mem τ) (X.B.w (vOf X τ))


variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in
theorem goodSRest_all {D : D7} {X : HidaSetting D} {θ : ℝ} (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D)
    (hT : Formalism.BasicNotions.dsigTie D) {C : Choice X θ} (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau) :
    GoodSRest hB u u' τ :=
  goodSRest_of_loc (Formalism.L2.SG.Pf.LocF.locFactor_holds hG C) hB u u' τ
    (Formalism.L2.SG.Pf.WuDec.lowSmoothSK (dsTr C τ) (isLowUnitH_base_vector C τ)) hT

end Formalism.L2.SG.Pf
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

section Gap

def GapEv {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ y : ℝ, ∀ x, y ≤ x → ∀ i : Fm.Ix x, Formalism.L2.SG.ConcreteSettingExists.GapHyp (Fm.D x i)

def CG (𝒞 : FamClass) : FamClass := fun Fm => 𝒞 Fm ∧ GapEv Fm

variable {𝒞 : FamClass} (sel : SSel 𝒞)

def selG : SSel (CG 𝒞) := fun Fm h => sel Fm h.1

def yFG : ∀ {eps : ℝ} (Fm : FamP eps), CG 𝒞 Fm → ℝ := fun _ h => Classical.choose h.2

theorem gap_of {eps : ℝ} {Fm : FamP eps} (h : CG 𝒞 Fm) {x : ℝ} (hx : yFG Fm h ≤ x) (i : Fm.Ix x) :
    Formalism.L2.SG.ConcreteSettingExists.GapHyp (Fm.D x i) :=
  Classical.choose_spec h.2 x hx i

theorem hyFG (hFX : Formalism.L2.SG.PoincareAmplitudeLowerBounds.FinXC) (hWu : Formalism.L2.SG.Pf.WuDecayOfGap) : YFOK (selG sel) yFG := by
  intro eps Fm hc x hx h0 hy i
  have hg := gap_of hc hy i
  exact ⟨hFX _ _ hg, (hWu _ hg _).1⟩

def CX {D : D7} (X : HidaSetting D) (u : D.what₂.Word) : Formalism.L2.SG.LocWSOf.Choice X 1 :=
  haveI : Nonempty D.what₂.Word := ⟨u⟩
  Classical.choice (Formalism.L2.SG.Pf.choiceExists X 1 one_pos)


theorem closed_sub {𝒞' : FamClass} (hs : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞' Fm → 𝒞 Fm)
    {P : ∀ {eps : ℝ}, FamP eps → ℝ → Prop} (h : Closed 𝒞 P) : Closed 𝒞' P := by
  obtain ⟨e, he, H⟩ := h
  exact ⟨e, he, fun eps h1 h2 => by
    obtain ⟨K, hK⟩ := H eps h1 h2
    exact ⟨K, fun Fm CH hc hL => hK Fm CH (hs Fm hc) hL⟩⟩

variable (C0 : ℝ)

theorem loopRowS_of_sub (hG : Closed 𝒞 fun Fm _ => 𝒞 Fm → GapEv Fm) (h : LoopRowS C0 (CG 𝒞) (selG sel)) :
    LoopRowS C0 𝒞 sel := by
  intro aF
  obtain ⟨e1, he1, H1⟩ := h aF
  obtain ⟨e2, he2, H2⟩ := hG
  refine ⟨min e1 e2, lt_min he1 he2, fun eps he hle => ?_⟩
  obtain ⟨K1, hK1⟩ := H1 eps he (hle.trans (min_le_left _ _))
  obtain ⟨K2, hK2⟩ := H2 eps he (hle.trans (min_le_right _ _))
  refine ⟨K1.sup K2, fun Fm CH hc hL => ?_⟩
  obtain ⟨hL1, hL2⟩ := (Fm.large_sup _ _ CH).1 hL
  intro hc'
  have hg := hK2 Fm CH hc hL2 hc'
  exact hK1 Fm CH ⟨hc', hg⟩ hL1 ⟨hc', hg⟩

end Gap

section PartC

variable {𝒞 : FamClass} (sel : SSel 𝒞)

def RMeasExAll : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (_root_.Formalism.L2.SG.PackageTie2.sOf hF))
    (C : Formalism.L2.SG.LocWSOf.Choice X 1) (u u' : D.what₂.Word),
    (∀ τ, GoodW D τ u u' 1 (Formalism.L2.SG.LocWSOf.locW C u u' τ)) → LoopTerm.RMeasEx hI C u u'

def JFactNAll : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (_root_.Formalism.L2.SG.PackageTie2.sOf hF))
    (C : Formalism.L2.SG.LocWSOf.Choice X 1) (hB : Formalism.L2.SG.LocWSOf.WuBessel C) (u u' : D.what₂.Word),
    Formalism.L2.SG.ConcreteSettingExists.GapHyp D → LoopTerm.JFactN hI C hB u u'


variable (C0 : ℝ)

end PartC

end Formalism.L2.SG.LoopsTies
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

section BM

variable (C0 : ℝ) {𝒞 : FamClass} (sel : SSel 𝒞) (yF : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → ℝ)

def YtR (hyF : YFOK sel yF) (C1f : List ℝ → ℝ)
    (B : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (_ : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word), LoopLocDat (Fm.D x i) (Fm.L x i) u u' (C1f Fm.cOut))
    (M : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word),
      LoopTermDat (Fm.D x i) (Fm.L x i) (AtR sel yF hyF Fm hc x hx i) u u' (C1f Fm.cOut) (B Fm hc x hx i u u'))
    {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) (x : ℝ) (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x)
    (u u' : (Fm.D x i).what₂.Word) :
    LoopTie (Fm.D x i) (Fm.L x i) (AtR sel yF hyF Fm hc x hx i) u u' (C1f Fm.cOut) :=
  loopTieOfParts
    (loopRowsOf (wOf ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X)
      (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1)
      (hOf _ _ _ _) (aOfW _ _ _ _ (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2)
      (hvOfW _ _ _ _ (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2)
      (Formalism.L2.SG.Pf.WittFlags.RowRepsIso_holds (Fm.D x i)) u u'
      (frameEqvInj_of _ _ (hOf _ _ _ _) (aOfW _ _ _ _ (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2)
        (hvOfW _ _ _ _ (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2)
        (Formalism.L2.SG.Pf.LoopBFrame.frameChangeC_holds _ _ _ _ _ _) u u'))
    (B Fm hc x hx i u u') (M Fm hc x hx i u u')

theorem tiesAt {D : D7} (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (_root_.Formalism.L2.SG.PackageTie2.sOf hF))
    (hWD : Formalism.L2.SG.WuDecay.WuDecay X) (u u' : D.what₂.Word) :
    Formalism.MainNotions.BridgeLemma₂.wordPairNormRelation (atOfW X Y hF hI hWD) u u' ∧ @Formalism.MainNotions.BridgeLemma.LatticeDeterminantFactorization D (atOfW X Y hF hI hWD) u u' ∧
      Formalism.MainNotions.BridgeLemma₂.wordPairEntriesInLattice (atOfW X Y hF hI hWD) u u' :=
  ⟨normTieC_holds D X Y hF hI (wOf X) (hOf X Y hF hI) (aOfW X Y hF hI hWD) (hvOfW X Y hF hI hWD) u u',
    Formalism.L2.SG.Pf.LoopBGenIdx.gram_determinant_relation D X Y hF hI (wOf X) (hOf X Y hF hI) (aOfW X Y hF hI hWD) (hvOfW X Y hF hI hWD) u u',
    entryLatC_holds D X Y hF hI (wOf X) (hOf X Y hF hI) (aOfW X Y hF hI hWD) (hvOfW X Y hF hI hWD) u u'⟩

theorem tiesR (hyF : YFOK sel yF) (C1f : List ℝ → ℝ)
    (B : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (_ : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word), LoopLocDat (Fm.D x i) (Fm.L x i) u u' (C1f Fm.cOut))
    (M : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word),
      LoopTermDat (Fm.D x i) (Fm.L x i) (AtR sel yF hyF Fm hc x hx i) u u' (C1f Fm.cOut) (B Fm hc x hx i u u'))
    {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) :
    Formalism.MainNotions.BridgeLemma₂.rows_TiesF (Fm.raise (yR sel yF Fm hc)) (C1f Fm.cOut) (AtR sel yF hyF Fm hc)
              (YtR sel yF hyF C1f B M Fm hc) ∧
      ∀ x (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
        Formalism.MainNotions.BridgeLemma₂.wordPairTermInjective (AtR sel yF hyF Fm hc x hx i) (YtR sel yF hyF C1f B M Fm hc x hx i u u') := by
  have hTI : ∀ x (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
      Formalism.MainNotions.BridgeLemma₂.wordPairTermInjective (AtR sel yF hyF Fm hc x hx i) (YtR sel yF hyF C1f B M Fm hc x hx i u u') :=
    fun x hx i u u' t t' hL hE => frameEqvInj_of (wOf ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X) (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1) (hOf ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).Y (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1 (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1))
      (aOfW ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).Y (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1 (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1) (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2)
      (hvOfW ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).Y (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1 (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1) (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2)
      (Formalism.L2.SG.Pf.LoopBFrame.frameChangeC_holds _ _ _ (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1 (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1) _) u u' t t' hL hE
  refine ⟨Formalism.MainNotions.BridgeLemma₂.family_gram_facts_of_hypotheses _ _ _ _ fun x hx i u u' =>
    ⟨(tiesAt ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).Y (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1 (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1) (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2 u u').1,
      (tiesAt ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).Y (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1 (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1) (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2 u u').2.1,
      (tiesAt ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).Y (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1 (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1) (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2 u u').2.2, hTI x hx i u u'⟩, hTI⟩


end BM

end Formalism.L2.SG.LoopsTies
end
end
