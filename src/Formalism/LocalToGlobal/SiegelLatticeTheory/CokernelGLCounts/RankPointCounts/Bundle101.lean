module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle061
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle100
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle024
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle099
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle080
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXHaarPos
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXSDLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXSIdx
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle051
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle056
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.VolPinAsm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LatBAsm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.ChartCG
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle093

@[expose] public section

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdConvCut2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol

theorem prodConv_holds_gen {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (hψ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ)
    (hloc : ∀ w : D.what₂.Word, LocCompatX X ψ w) (u u' : D.what₂.Word) : ProdConv X u u' ψ :=
  prodConvNew_holds_gen X hb ψ hψ hs hloc u u'

theorem prodConv_holds {D : D7} (T : Formalism.L2.SG.SpectralTiesReal.STies D) (u u' : D.what₂.Word) : ProdConv T.X u u' T.ψ :=
  prodConv_holds_gen T.X T.hb T.ψ T.ψ_char T.ψ_std T.locCompat u u'

theorem prodConvAll_holds : Formalism.L2.SG.PoincareAmplitudeLowerBounds.ProdConvAll :=
  fun _ T u u' _ _ => prodConv_holds T u u'

theorem prodConv_onTied :
    Formalism.L2.SG.NGAnalytic.MassDataLemmas.OnTied fun _ X _ _ u u' _ ψ => ProdConv X u u' ψ := by
  intro Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' _ hb X0 ψ hT
  exact prodConv_holds_gen X hb ψ hT.2.1 hT.2.2.1 hT.2.2.2.2.1 u u'

end Formalism.L2.SG.Pf.ProdConvCut2
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocVol
  Formalism.L2.SG.NGAnalytic.MassDataLemmas

namespace Formalism.L2.SG.Pf.MassDataX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem nTy_holds : OnTied fun D X hb Y u u' X0 ψ =>
    Formalism.L2.SG.MassDataConc.InTypedC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u)
      (fun _ => 0) (pairSys0 u u' (X.Fu u) (Y.what₂ u)) Y.M Y.δ (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0) := by
  intro _ _ _ _ _ _ _ _ D _ X Y u u' _ hb X0 ψ hT
  exact inTypedC_loc X hb Y.hK _ _ u u' X0 ψ _ 0 0 1 _ _ _ _ _ _ _
    (fun X v => SDL.sdLocX_holds X v) (fun X v _ => Formalism.L2.SG.Pf.NcX.OmVSt.unramAt_of_cm X.B.I.cm v) sTypIdx_holds
    hT.2.1 hT.2.2.1

theorem frameVolAt_of_prodConv (hP : OnTied fun _ X _ _ u u' _ ψ => ProdConv X u u' ψ) : OnTied fun D X hb Y u u' X0 ψ =>
    FrameVolAt X hb Y u u' X0 ψ 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u) (fun _ => 0)
      (pairSys0 u u' (X.Fu u) (Y.what₂ u)) (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0) := by
  intro Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hCtx hb X0 ψ hT
  exact frameVolAt_of X hb Y u u' X0 ψ 0 0 1 _ _ _ _ _ hT.2.1 hT.2.2.1
    (hP Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hCtx hb X0 ψ hT)

theorem nPos_of (hSW : PI.VolStabS.MassDataS.SWXS) (hP : OnTied fun _ X _ _ u u' _ ψ => ProdConv X u u' ψ) :
    OnTied fun _ X hb Y u u' X0 ψ => (bk0 X hb Y u u' X0 ψ).Pos := by
  intro Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hCtx hb X0 ψ hT
  have hK2 := Formalism.L2.SG.Closed.level_subgroup_properties X
  have hV : 0 < X.volK2 := ENNReal.toReal_pos (ne_of_gt hK2.2.2.1) (ne_of_lt hK2.2.2.2)
  have hH : Formalism.L2.SG.TypedSets.HypX X hb (Y.FN u) (Y.FN u') u u' :=
    ⟨hT.1, hCtx.2.2.1, Y.FN_fund u, Y.FN_fund u'⟩
  exact Formalism.L2.SG.Pf.MassDataPos.massDataPosC_of X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1
    (fun _ => 0) (pairSys0 u u' (X.Fu u) (Y.what₂ u)) Y.M Y.δ (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0)
    (locHaarPosC_holds X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 _ _ Y.M Y.δ _ _ _)
    (covolPosC_of X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 _ _ Y.M Y.δ _ _ _ hSW hT.2.1 hT.2.2.2.1
      hT.1 hT.2.2.2.2.2.2)
    (Formalism.L2.SG.Pf.MassDataPos.quotVolPosC_of X hb Y u u' X0 ψ (Y.tO u u') 0 0 1 _ _ Y.M Y.δ _ _ _ hK2 hV)
    (recPosC_of_dv X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 _ _ Y.M Y.δ _ _ _
      (fun X v => dvPosC_holds X v) hH)
    (hP Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hCtx hb X0 ψ hT) (Formalism.L2.SG.Pf.MassDataPos.cooOf_pos X u u')
    (Formalism.L2.SG.WConst.kapN_pos (D := D)) le_rfl le_rfl one_pos

end Formalism.L2.SG.Pf.MassDataX
end
end

section

noncomputable section

open scoped Classical
open ValuativeRel

namespace Formalism.L2.SG.Pf.MassDataX

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.DataInst Formalism.L2.SG.CntLocal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem one_sub_eta_nonneg (η : ℝ) (hη : η = 1 ∨ η = -1) (q i : ℕ) : 0 ≤ 1 - η ^ i / ((q : ℕ) : ℝ) ^ i := by
  have h1 : |η ^ i| = 1 := by
    rcases hη with rfl | rfl <;> simp [abs_pow]
  rcases Nat.eq_zero_or_pos (q ^ i) with h | h
  · have h' : ((q : ℕ) : ℝ) ^ i = 0 := by exact_mod_cast h
    rw [h', div_zero]
    norm_num
  · have h' : (1 : ℝ) ≤ ((q : ℕ) : ℝ) ^ i := by exact_mod_cast (show 1 ≤ q ^ i from h)
    have h2 : η ^ i / ((q : ℕ) : ℝ) ^ i ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact (le_abs_self _).trans (h1.le.trans h')
    linarith

theorem etaP_pm {D : D7} (p : PlF D) : eta₃ p = 1 ∨ eta₃ p = -1 := by
  unfold eta₃
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem aPD_nonneg {D : D7} (p : PlF D) (T : ℕ) : 0 ≤ aPD p T := by
  unfold aPD
  apply Finset.prod_nonneg
  intro i _
  exact one_sub_eta_nonneg _ (etaP_pm p) _ _

theorem alpD_nonneg {D : D7} (u u' : D.what₂.Word) (p : PlF D) : 0 ≤ alpD u u' p := by
  unfold alpD
  split_ifs
  · exact aPD_nonneg p _
  · exact mul_nonneg (aPD_nonneg p _) (aPD_nonneg p _)

theorem densP_nonneg {D : D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (L : LocSp D M)
    (δ : ∀ p : PlF D, (D.s.atP p).Fp) (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]) (T T' : D.host.E) (Z : MatZ D) (p : PlF D) :
    0 ≤ densP L δ ϖ T T' Z p := by
  unfold densP Formalism.MainNotions.S.Loc.HermSp.dens
  positivity

theorem densNonnegAll_holds : Formalism.L2.SG.PoincareAmplitudeLowerBounds.DensNonnegAll := by
  intro D T u u' Lsp ϖ
  apply div_nonneg
  · unfold supDens
    apply Real.sSup_nonneg
    intro d hd
    simp only [densSet, Set.mem_setOf_eq] at hd
    obtain ⟨Z, -, rfl⟩ := hd
    exact tprod_nonneg fun p => densP_nonneg _ _ _ _ _ _ _
  · exact tprod_nonneg fun p => alpD_nonneg u u' p

end Formalism.L2.SG.Pf.MassDataX
end
end

section

namespace Formalism.L2.SG.NGCut.StabilizerCovolume

theorem covolOne3C_holds : Formalism.L2.SG.Pf.VolPinAsm.CovolOne3C :=
  covolOne3C_of Formalism.L2.S.Pv.Chart.chartC_holds (stabilizerLatticeCoordinates_of Formalism.L2.SG.LatBAsm.stabilizer_lattice_twisted_prod)

end Formalism.L2.SG.NGCut.StabilizerCovolume
end
