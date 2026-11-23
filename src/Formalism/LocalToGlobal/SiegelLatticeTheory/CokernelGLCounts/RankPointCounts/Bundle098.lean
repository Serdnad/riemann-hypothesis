module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle024
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocVolPrim
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle097
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle040
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXHaarPos
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXSDLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle094
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle007
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocMassTyp
import Aesop.Main
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIE
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIIota
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle092
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaK
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaRat
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle096
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle033
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.InVolumesAtOfSWW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.StepFrameStd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.StepSize
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.Bundle004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle052
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle068
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle054
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle035
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle035

@[expose] public section

section

noncomputable section

open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.ProdConvCut2

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.MassDataX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem local_factors_pos_typical_general {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (ψ : AddChar (AF X.B.I.F) ℂ)
    (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ) (hloc : ∀ w : D.what₂.Word, LocCompatX X ψ w)
    (u u' : D.what₂.Word) (v : PlX X) (hv : TypAt X v) : 0 < MX X u u' ψ v ∧ 0 < localVolumeUnit X ψ v := by
  let p : TypX X := ⟨v, hv⟩
  have : Submodule.IsFullLattice X.B.I.E X.B.I.L :=
    { toIsLattice := Submodule.IsLattice.of_fg X.B.I.E X.B.I.L_fg
      span_eq_top := X.B.I.L_span }
  have hL := locTieX_of X ψ u (hloc u) (Formalism.L2.SG.Pf.LocVolPrim.primX X u locFramePrim)
  have hL' := locTieX_of X ψ u' (hloc u') (Formalism.L2.SG.Pf.LocVolPrim.primX X u' locFramePrim)
  have hTF := Formalism.L2.SG.Pf.typFacts_holds X hb u u'
  have h := locMassTyp X.B.I.cm.sig X.B.I.J ψ v (gAt X v) (frameOf X u) (frameOf X u')
    (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))
    ⟨MassDataVolumesW.stepCM X, MassDataVolumesW.stepHerm X, hψ, hs⟩ _ _
    (MassDataLevelSSteps.FrameW.frameOf_isStd X u) (MassDataLevelSSteps.FrameW.frameOf_isStd X u')
    (Formalism.L2.SG.Pf.MassDataX.SDL.sdLocX_holds X v) (Formalism.L2.SG.Pf.NcX.OmVSt.unramAt_of_cm X.B.I.cm v)
    ⟨X.B.I.L, inferInstance, rfl⟩ (hTF p).1
    (gAt_mem X p) (hTF p).2.1 (hTF p).2.2.1 (hTF p).2.2.2.2
    _ (hL v).1 _ (hL v).2.1 (hL v).2.2.1 _ (hL' v).2.1 (hL' v).2.2.1 (hL v).2.2.2 (hL' v).2.2.2
  have hpos := div_pos (mul_pos (gv_pos X p (kg_sub_kv X p) subset_rfl)
      (gv_pos X p (kg_sub_knat X p u) (knat_sub_kv X p u)))
      (mul_pos (sv_pos X u p (kg_sub_kv X p) subset_rfl) (sv_pos X u' p (kg_sub_kv X p) subset_rfl))
  have hR : 0 < MX X u u' ψ v / localVolumeUnit X ψ v := by
    unfold MX localVolumeUnit OmX
    rw [if_pos hv, if_pos hv]
    exact lt_of_lt_of_eq hpos h.symm
  have hU0 : 0 ≤ localVolumeUnit X ψ v := ENNReal.toReal_nonneg
  rcases div_pos_iff.1 hR with ⟨h1, h2⟩ | ⟨-, h2⟩
  · exact ⟨h1, h2⟩
  · exact absurd h2 (not_lt.2 hU0)

end Formalism.L2.SG.Pf.ProdConvCut2
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.MassDataX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Measures Formalism.L2.SG.Volumes MeasureTheory MassDataVolumesW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem covolH_eq_volG (hSW : PI.VolStabS.MassDataS.SWXS) {D : D7} (X : HidaSetting D)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (hψ : IsCharAF X.B.I.F ψ) (hC : MeasCompatψ X ψ)
    (w : D.what₂.Word) :
    covol (X.measW w).μH = covolBy (G := HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) (HFinIn (AF X.B.I.F) X.B.I.cm.sig X.B.I.J)
      X.measG.μG := by
  have hs := stepSizeW X
  obtain ⟨⟨hT1, νH, hνH, hcH⟩, -⟩ := hC.1 w
  exact covol_eq_covolBy_w (PI.VolStabS.MassDataS.volStabXS_of hSW X) (stepHerm X) (a := D.R.rS + 1 + D.R.rS)
    (by omega) (by omega) _ hT1 (stepGramH_of MassDataLevelSSteps.frameStd_holds X w hT1) hψ X.measG_norm.1 hνH
    (X.measW_norm w).1 hcH

section MassData

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem volHa'_eq (hSW : PI.VolStabS.MassDataS.SWXS) (hψ : IsCharAF X.B.I.F ψ) (hC : MeasCompatψ X ψ) :
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volHa' =
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volG :=
  covolH_eq_volG hSW X ψ hψ hC u'

end MassData

end Formalism.L2.SG.Pf.MassDataX
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf
open scoped ENNReal

namespace Formalism.L2.SG.RootPatterns

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.RealConjugatorData

variable {D : D7}

theorem blockIdx_loc (ρ : ℕ → ℕ → ℝ) (v : D.what₂.Tau) :
    ∀ (bs : List (D.host.E × ℕ)) (a i : ℕ), blockIdx (locBlocksFrom D ρ v a bs) i = Formalism.L2.SG.RealObj.blkOf bs i
  | [], _, _ => rfl
  | (t, s) :: bs, a, i => by
    simp only [locBlocksFrom, blockIdx, Formalism.L2.SG.RealObj.blkOf]
    split_ifs
    · rfl
    · rw [blockIdx_loc ρ v bs (a + s) (i - s), add_comm]

theorem mem_rootPat_iff (τ : D.what₂.Tau) (w : Point D.host.E (D.R.rS + 1)) (q : Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) :
    q ∈ rootPat (ptLoc D τ w) ↔ q.1 < q.2 ∧ Formalism.L2.SG.RealObj.blkOf w.1 q.1.1 = Formalism.L2.SG.RealObj.blkOf w.1 q.2.1 := by
  simp only [rootPat, ptLoc, ptLocS, locBlocks, Set.mem_setOf_eq, blockIdx_loc]
  simp [Set.mem_toFinset, Finset.mem_filter, Finset.mem_univ]

def idxF (τ : D.what₂.Tau) (w : Point D.host.E (D.R.rS + 1)) : ↥(rootPat (ptLoc D τ w)) ≃ Formalism.L2.SG.RealObj.FreeE w where
  toFun q := ⟨q.1, (mem_rootPat_iff τ w q.1).1 q.2⟩
  invFun q := ⟨q.1, (mem_rootPat_iff τ w q.1).2 q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem rootCoords_cont (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (p : Point ℂ (r + 1)) :
    Continuous (rootCoords k r z p) := by
  unfold Formalism.MainNotions.S.rootCoords
  refine continuous_pi (fun q => ?_)
  unfold flagMat
  first
    | fun_prop
    | (simp only [Matrix.mul_apply, Matrix.of_apply]; fun_prop)
    | continuity
    | (exact ((continuous_apply _).comp (continuous_apply _)).comp
        (Continuous.matrix_mul (Continuous.matrix_mul continuous_const continuous_id) continuous_const))

variable {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
  (γ : X.B.I.Ginf) (τ : D.what₂.Tau)

theorem stCoordV_comp :
    Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ) =
      (MeasurableEquiv.piCongrLeft (fun _ : Formalism.L2.SG.RealObj.FreeE w => ℂ) (idxF τ w)) ∘
        rootCoords D.R.k D.R.rS (zB X (C.Qi τ) u' τ) (ptLoc D τ w) ∘ cMr C γ τ := by
  funext y q
  have ha : q.1.1.1 < D.R.rS := by have := q.2.1; have := q.1.2.isLt; omega
  have hpc : ∀ x : ↥(rootPat (ptLoc D τ w)) → ℂ,
      MeasurableEquiv.piCongrLeft (fun _ : Formalism.L2.SG.RealObj.FreeE w => ℂ) (idxF τ w) x q = x ((idxF τ w).symm q) :=
    fun x => by simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  simp only [Function.comp_apply]
  rw [hpc, Formalism.L2.SG.RealFrameCoordinates.stCoordV_eq C u' w γ τ y q]
  unfold rootCoords flagMat
  rw [dite_eq_left (show ((idxF τ w).symm q).1.1.val < D.R.rS from ha), ← cMr_eq]
  rfl


include C in
theorem place (hLoc : Formalism.L2.SG.NGPin.LocRootHaar) (hrep : Formalism.L2.SG.RealObj.IsPtRep X u u' w γ) :
    ∃ (μ : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) (c : ℝ≥0∞),
      Formalism.L2.SG.RealObj.IsHaarLoc (Formalism.L2.SG.NGPin.StV X u u' γ (vOf X τ)) μ ∧ c ≠ 0 ∧ c ≠ ⊤ ∧
        μ.map (Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ)) =
          c • Measure.pi (fun _ : Formalism.L2.SG.RealObj.FreeE w => (volume : Measure ℂ)) := by
  obtain ⟨hzW, hTz⟩ := Formalism.L2.SG.Pf.zTr C u τ
  obtain ⟨hzW', hTz'⟩ := Formalism.L2.SG.Pf.zTr C u' τ
  have hT : ∀ u0 : D.what₂.Word, 0 < Tr D u0 := fun u0 => by
    unfold Tr
    exact Nat.cast_pos.2 (D.mem u0).A.T_prime.pos
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hg0 : Formalism.L2.SG.RealFrameCoordinates.g0 C γ τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) :=
    Formalism.L2.SG.Pf.LTL.trG_mem _ _ _ (C.isT τ).2.1 (C.isT τ).2.2.1 _
  obtain ⟨μ₀, c, hHaar, hc0, hctop, hmap⟩ := hLoc D.R.k D.R.rS hk _ _ hzW (by rw [hTz]; exact hT u) hzW'
    (by rw [hTz']; exact hT u') (ptLoc D τ w) _ hg0 (Formalism.L2.SG.RealFrameCoordinates.zhat_conjugator_eq_point C u u' w γ hrep τ)
  have hemb := cMr_measEmb C γ τ
  set μ := Measure.comap (cMr C γ τ) μ₀ with hμ
  have hconc : μ₀ (Set.range (cMr C γ τ))ᶜ = 0 := by
    refine measure_mono_null (fun x hx => ?_) hHaar.2.2.1
    intro hR
    exact hx (rset_range C γ τ x hR)
  have hres : μ₀.restrict (Set.range (cMr C γ τ)) = μ₀ := Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hconc)
  have hmapc : μ.map (cMr C γ τ) = μ₀ := by rw [hμ, hemb.map_comap, hres]
  have : SigmaFinite μ₀ := hHaar.1
  refine ⟨μ, c, ⟨?_, ?_, ?_, fun s hs => ?_⟩, hc0, hctop, ?_⟩
  · exact SigmaFinite.of_map μ hemb.measurable.aemeasurable (by rw [hmapc]; infer_instance)
  · intro h0
    apply hHaar.2.1
    rw [← hmapc, h0, Measure.map_zero]
  · rw [hμ, hemb.comap_apply]
    refine measure_mono_null ?_ hHaar.2.2.1
    rintro _ ⟨y, hy, rfl⟩ hR
    exact hy ((stV_iff C γ τ u u' y).2 hR)
  · have hs0 := (stV_iff C γ τ u u' s).1 hs
    have hfun : cMr C γ τ ∘ (fun x => s * x) = Formalism.QuantumDeterminants.lmulM (cMr C γ τ s) ∘ cMr C γ τ := by
      funext x
      obtain ⟨hQiQ, hQQi, _, _⟩ := C.isT τ
      show C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat (s * x) * (uMat (γ (vOf X τ)) * C.Q τ) =
        (C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat s * (uMat (γ (vOf X τ)) * C.Q τ)) *
          (C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat x * (uMat (γ (vOf X τ)) * C.Q τ))
      rw [show uMat (s * x) = uMat s * uMat x from rfl]
      calc C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * (uMat s * uMat x) * (uMat (γ (vOf X τ)) * C.Q τ)
          = C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat s * ((uMat (γ (vOf X τ)) * (C.Q τ * C.Qi τ) *
              (uMat (γ (vOf X τ)))⁻¹) * uMat x) * (uMat (γ (vOf X τ)) * C.Q τ) := by
            rw [hQQi, Matrix.mul_one, uMat_mul_inv, Matrix.one_mul]
            simp only [Matrix.mul_assoc]
        _ = _ := by simp only [Matrix.mul_assoc]
    have hmeas_s : Measurable (fun x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => s * x) := measurable_const_mul s
    have hmeas_l : Measurable (Formalism.QuantumDeterminants.lmulM (k := D.R.k) (r := D.R.rS) (cMr C γ τ s)) := by
      refine Continuous.measurable ?_
      unfold Formalism.QuantumDeterminants.lmulM
      refine Continuous.matrix_mul continuous_const ?_
      exact continuous_id
    have key : (μ.map (fun x => s * x)).map (cMr C γ τ) = μ.map (cMr C γ τ) := by
      rw [Measure.map_map hemb.measurable hmeas_s, hfun, ← Measure.map_map hmeas_l hemb.measurable, hmapc]
      exact hHaar.2.2.2 _ hs0
    calc μ.map (fun x => s * x) = (((μ.map (fun x => s * x)).map (cMr C γ τ))).comap (cMr C γ τ) :=
          (hemb.comap_map _).symm
      _ = μ := by rw [key, hemb.comap_map]
  · rw [stCoordV_comp C u' w γ τ, ← Measure.map_map (MeasurableEquiv.piCongrLeft _ _).measurable
      ((rootCoords_cont _ _ _ _).measurable.comp hemb.measurable),
      ← Measure.map_map (rootCoords_cont _ _ _ _).measurable hemb.measurable, hmapc, hmap, Measure.map_smul,
      (volume_measurePreserving_piCongrLeft (fun _ : Formalism.L2.SG.RealObj.FreeE w => ℂ) (idxF τ w)).map_eq]
    · rfl
    · exact (MeasurableEquiv.piCongrLeft _ _).measurable.aemeasurable

theorem placeHaar_of_loc (hLoc : Formalism.L2.SG.NGPin.LocRootHaar) : Formalism.L2.SG.NGPin.PlaceHaar := by
  intro D X u u' w γ hrep v
  have : Nonempty D.what₂.Word := ⟨u⟩
  obtain ⟨C⟩ := Formalism.L2.SG.Pf.choiceExists X 1 one_pos
  obtain ⟨τ, rfl⟩ : ∃ τ, vOf X τ = v := ⟨X.pl v, X.pl.symm_apply_apply v⟩
  exact place C u u' w γ τ hLoc hrep

end Formalism.L2.SG.RootPatterns

end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut
  Formalism.L2.SG.Pf.StabShape Formalism.L2.SG.Pf.ProdEP2Core

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) {p : PlF D}

section Parts2

variable (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U)
  (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (hB : BaseAt M δ u u' w p a) (πa : UP p →* UP p)
  (hD : CountAb.Data a.mat (MulAction.stabilizer (UP p) a.mat) πa.ker (KU M p) πa)

theorem img_eq :
    img (retr_of M δ u u' w p a πa hD hB) (KP M p ⊓ StabX p (XP M δ u u' (p := p) w L U)) (H_le_UP M _) =
      (((CountAb.Hs a.mat (KU M p) (gU M δ u u' w hA L U hL hU a hB)).map πa).map (tauU p)).map (UP p).subtype := by
  ext z
  constructor
  · rintro ⟨h, hh, rfl⟩
    have hU' := H_le_UP M _ hh
    have hy := (mem_H_iff M δ u u' w hA L U hL hU a hB ⟨h, hU'⟩).1 hh
    refine ⟨tauU p (πa (tauU p ⟨h, hU'⟩)), ⟨πa (tauU p ⟨h, hU'⟩), ⟨_, hy, rfl⟩, rfl⟩, ?_⟩
    exact (piG_of p πa ⟨h, hU'⟩).symm
  · rintro ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    refine ⟨((tauU p y : UP p) : GG p), ?_, ?_⟩
    · exact (mem_H_iff M δ u u' w hA L U hL hU a hB (tauU p y)).2 (by rw [tauU_tauU]; exact hy)
    · show piG p πa ((tauU p y : UP p) : GG p) = _
      rw [piG_of]
      simp only [piU, MonoidHom.comp_apply, tauU_tauU]
      rfl

include hB in
theorem Ag_eq :
    Ag M δ u u' (p := p) w =
      (((KU M p) ⊓ MulAction.stabilizer (UP p) a.mat).map (tauU p)).map (UP p).subtype := by
  ext z
  rw [mem_Ag_iff]
  constructor
  · rintro ⟨hS, hK⟩
    obtain ⟨hzU, hzY⟩ := (mem_StP_iff M δ u u' w p z).1 hS
    have hfix := (fixes_base_iff M δ u u' w p a hB ⟨z, hzU⟩).1 hzY
    refine ⟨⟨z, hzU⟩, ⟨tauU p ⟨z, hzU⟩, ⟨?_, ?_⟩, tauU_tauU p _⟩, rfl⟩
    · show ((tauU p ⟨z, hzU⟩ : UP p) : GG p) ∈ KP M p
      exact tau_mem_KP M p hK
    · exact hfix
  · rintro ⟨_, ⟨y, ⟨hyK, hyS⟩, rfl⟩, rfl⟩
    refine ⟨(mem_StP_iff M δ u u' w p _).2 ⟨(tauU p y).2, ?_⟩, ?_⟩
    · exact (fixes_base_iff M δ u u' w p a hB (tauU p y)).2 (by rw [tauU_tauU]; exact hyS)
    · exact tau_mem_KP M p hyK


include hD in
theorem countAt_of_parts (v : ℝ)
    (hv : (Nat.card (Quotient (CountAb.cellRel a.mat πa.ker (KU M p) (gU M δ u u' w hA L U hL hU a hB))) : ℝ) = v)
    (hpos : Nat.card (Quotient (CountAb.cellRel a.mat πa.ker (KU M p) (gU M δ u u' w hA L U hL hU a hB))) ≠ 0) :
    CountAt M δ u u' w hA L U hL hU v := by
  have hcard := CountAb.card_cells' (a.mat) (MulAction.stabilizer (UP p) a.mat) πa.ker (KU M p) πa
    (gU M δ u u' w hA L U hL hU a hB) hD
  have hidx : (img (retr_of M δ u u' w p a πa hD hB) (KP M p ⊓ StabX p (XP M δ u u' (p := p) w L U))
      (H_le_UP M _)).relIndex (Ag M δ u u' (p := p) w) =
      ((CountAb.Hs a.mat (KU M p) (gU M δ u u' w hA L U hL hU a hB)).map πa).relIndex
        ((KU M p) ⊓ MulAction.stabilizer (UP p) a.mat) := by
    rw [img_eq M δ u u' w hA L U hL hU a hB πa hD, Ag_eq M δ u u' w a hB,
      Subgroup.relIndex_map_map_of_injective _ _ Subtype.val_injective,
      Subgroup.relIndex_map_map_of_injective _ _ (tauU_inj (p := p))]
  refine ⟨UP p, piG p πa, retr_of M δ u u' w p a πa hD hB, H_le_UP M _, conjugator_mem_unipotent M δ hA L U hL hU, ?_, ?_, ?_⟩
  · rw [img_eq M δ u u' w hA L U hL hU a hB πa hD, Ag_eq M δ u u' w a hB]
    apply Subgroup.map_mono
    apply Subgroup.map_mono
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨hD.kπ z hz.1, hD.mem z⟩
  · rw [hidx, ← hcard]
    exact hpos
  · rw [hidx, ← hcard, hv]

end Parts2

end Formalism.L2.SG.Pf.CountAt
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

theorem pinB_holds : PinB Zd u u' F0 what₂ :=
  pinB_of Zd (spanOm_holds D) (pinOm_holds Zd u u' F0 what₂) (localOrthogonal_holds Zd)

theorem betaInt_holds : BetaInt Zd u u' F0 what₂ :=
  betaInt_of Zd (lsetB_of Zd (pinB_holds Zd u u' F0 what₂)) (iotaB_of Zd (pinB_holds Zd u u' F0 what₂))

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem fStarC_of_int (hC : CtxP u u' F0 what₂) (hInt : BetaInt Zd u u' F0 what₂) : FStarC Zd u u' F0 what₂ :=
  fStarC_of_beta Zd hC (betaRat_holds Zd u u' F0 what₂) hInt

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

namespace Formalism.L2.SG.Pf.MassDataX

theorem massDataVolAll_of (hSW : PI.VolStabS.MassDataS.SWXS) :
    Formalism.L2.SG.PoincareAmplitudeLowerBounds.MassDataVolAll := by
  intro D T u u' X0 sd C Th Q i0 i0' νq
  refine ⟨PI.VolStabS.MassDataS.inVolumesAt_of_SWS hSW _ _ _ _ _ _ _ _ _ _, ?_, ?_, ?_, ?_⟩
  · first
      | apply level_s_at_instance
      | apply PI.Final.level_s_at_instance
      | apply PI.level_s_at_instance
      | apply MassDataLevelSSteps.inLevelSAt_holds
      | apply PI.MassDataLevelSSteps.inLevelSAt_holds
      | apply PI.UnitaryGroupMassFormula.MassDataLevelSSteps.inLevelSAt_holds
  · apply inMassesAt_holds
  · apply inColumnsAt_holds
  · apply inIndicesAt_holds

end Formalism.L2.SG.Pf.MassDataX
end
