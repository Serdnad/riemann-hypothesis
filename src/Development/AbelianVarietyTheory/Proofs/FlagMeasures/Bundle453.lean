module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle427
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle016
public import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle015
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle432
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmpBoundsUniformOfInputs
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle437
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle284
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsWordLetters
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle300
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowDoubleCosetSumNormSqBound
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowWeightsLocalOrbitsSumEqGenusMass
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle452
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle339
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FormAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelCharPfRat
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpFibreConstOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocJEqMeas
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle431
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle342
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle442
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NormalizingConstantEq
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf

@[expose] public section

section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.normalizedFormalDegree_eq_vandermonde_of_sizes : ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ), thr ≤ C' → thr ≤ Cl → Ties D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → DataNW D → ∀ τ, VV D τ = vand (lamSH D.R (D.hc τ)) := by
  first | exact @GlobalTheory.Core.Deg.CritVand.vv_eq_vand_of_sizes | exact GlobalTheory.Core.Deg.CritVand.vv_eq_vand_of_sizes | (intros; apply GlobalTheory.Core.Deg.CritVand.vv_eq_vand_of_sizes <;> assumption)
end

section

noncomputable section
open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf
namespace GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem factC_of (hP : PullC) (hTn : TensC) (hC : ConstC) : FactC := by
  intro D X Y u C hB hG hcov t hrel μ ν K hμν hK
  obtain ⟨μR, νl, hνl, hH, hQ, hμR, hmap⟩ := hP D X Y u C t μ ν hμν
  have hFA := Formalism.L2.SG.Pf.formAllC_holds D X Y u u t μR (Measure.pi νl) K
    (Formalism.L2.SG.Pf.RelChar.relCharC_holds D X Y u u t hrel) hH hQ hK.1 hK.2
  have hT := hTn D X u t.pt.1 νl hνl
  obtain ⟨hc, hconst⟩ := hC D X Y u C hB hG hcov
  have hloc : ∀ τ, Real.sqrt (hsNormSq ((locS hB u u τ).J (ν τ) (gamT C t τ))) =
      (cOf hB u τ)⁻¹ * Real.sqrt (hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ))
        Formalism.L2.SG.RealObj.Jv (νl (vOf X τ)) (X.Wloc u (vOf X τ)) (X.Wloc u (vOf X τ)) (t.pt.1 (vOf X τ)))) := by
    intro τ
    rw [← hmap τ]
    unfold gamT
    rw [Formalism.L2.SG.Pf.LocJEq.locJ_map_eq' C hB u u τ]
    refine (congrArg Real.sqrt (Formalism.L2.SG.Pf.LTL.hsNormSq_smul _ _)).trans ?_
    rw [(hc τ).2, mul_one, map_inv₀, Complex.normSq_ofReal, Real.sqrt_mul', Real.sqrt_inv,
      Real.sqrt_mul_self (hc τ).1.le]
    · rfl
    · exact Formalism.L2.SG.Pf.LTL.hsNormSq_nonneg _
  have hv : ‖(Y.tO u u).vec t‖ = wt t * ‖Formalism.L2.SG.PackageTie.hsEmb
      (ampN (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t)‖ := by
    show ‖Formalism.L2.SG.TermOp.vec (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t‖ = _
    unfold Formalism.L2.SG.TermOp.vec
    rw [← norm_smul_of_nonneg (show 0 ≤ wt t from Real.sqrt_nonneg _) (Formalism.L2.SG.PackageTie.hsEmb
      (ampN (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t)), ← Complex.coe_smul]
    refine Eq.trans ?_ (PiLp.norm_single 2
      (fun _ : {Λ // Λ ∈ Y.what₂ u} × {Λ' // Λ' ∈ Y.what₂ u} => Formalism.L2.SG.PackageTie.HS (X.Vpi u) (X.Vpi u))
      ((⟨t.lam, t.mem⟩, ⟨t.lam', t.mem'⟩) : {Λ // Λ ∈ Y.what₂ u} × {Λ' // Λ' ∈ Y.what₂ u}) _)
    congr 2
    ext q
    simp [Pi.single_apply]
  have hs0 : 0 ≤ scl (Y.FN u) (Y.FN u) (X := X) (u := u) (u' := u) * X.volK2 := by
    unfold scl HidaSetting.volK2
    positivity
  have hamp : ‖Formalism.L2.SG.PackageTie.hsEmb (ampN (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t)‖ =
      (scl (Y.FN u) (Y.FN u) (X := X) (u := u) (u' := u) * X.volK2) * ((μR K).toReal *
        ‖Formalism.L2.SG.PackageTie.hsEmb (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
          OO (Measure.pi νl) Set.univ (X.Wu u) (X.Wu u) t.pt.1)‖) := by
    unfold ampN
    rw [map_smul, map_smul, norm_smul, norm_smul, Formalism.L2.SG.Pf.FibreCounting.norm_chiN, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hs0, hFA, ← Complex.coe_smul, map_smul, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  have hprod : ∏ τ, Real.sqrt (hsNormSq ((locS hB u u τ).J (ν τ) (gamT C t τ))) =
      (∏ τ, cOf hB u τ)⁻¹ * ∏ v, Real.sqrt (hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
        Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u v) (t.pt.1 v))) := by
    rw [Finset.prod_congr rfl fun τ _ => hloc τ, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    congr 1
    exact Fintype.prod_equiv X.pl.symm _ _ (fun τ => rfl)
  have hPc : 0 < ∏ τ, cOf hB u τ := Finset.prod_pos fun τ _ => (hc τ).1
  rw [hv, hamp, ← hμR K hK.1, hprod]
  set N := ‖Formalism.L2.SG.PackageTie.hsEmb (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
          OO (Measure.pi νl) Set.univ (X.Wu u) (X.Wu u) t.pt.1)‖ with hN
  set Pv := ∏ v, Real.sqrt (hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
        Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u v) (t.pt.1 v))) with hPv
  set Pc := ∏ τ, cOf hB u τ with hPcd
  set s := scl (Y.FN u) (Y.FN u) (X := X) (u := u) (u' := u) * X.volK2 with hsd
  set a := wt t with had
  set m := (μR K).toReal with hmd
  set cv := (covN C Y u).toReal with hcv
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hm : 0 ≤ m := ENNReal.toReal_nonneg
  have hcv0 : 0 ≤ cv := ENNReal.toReal_nonneg
  have hPv0 : 0 ≤ Pv := Finset.prod_nonneg fun v _ => Real.sqrt_nonneg _
  have hNP : N ≤ Pv := hT
  have hSJ : 0 ≤ Pc⁻¹ * Pv := mul_nonneg (inv_nonneg.2 hPc.le) hPv0
  calc a * (s * (m * N)) * cv = (a * m * cv * s) * N := by ring
    _ ≤ (a * m * cv * s) * (Pc * (Pc⁻¹ * Pv)) := by
        rw [mul_inv_cancel_left₀ hPc.ne']
        exact mul_le_mul_of_nonneg_left hNP (by positivity)
    _ = (a * (m * (Pc⁻¹ * Pv))) * (s * Pc * cv) := by ring
    _ ≤ (a * (m * (Pc⁻¹ * Pv))) * 1 := mul_le_mul_of_nonneg_left hconst (by positivity)
    _ = a * (m * (Pc⁻¹ * Pv)) := mul_one _

theorem factC_holds : FactC := factC_of GlobalTheory.T.localHaarMeasures_pullback_realGroup GlobalTheory.T.orbitalIntegralTensorBoundHyp_proof GlobalTheory.T.normalisingConstantsProductHyp_proof

end GlobalTheory.TypeAsm
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.GapAmpUniform

theorem weyl_fam_gap : ∀ (eps : ℝ) (Fm : FamP eps), VanishingOnXAndXPlusBranching.FamilyTwelfthHypothesis Fm := by
  intro eps Fm x i τ w H _ _ z π hπ
  obtain ⟨g, -, hg⟩ := hπ
  exact (GlobalTheory.WeylDimU.weyl_dimension _ _ (GlobalTheory.CritLevel.isHCParam_uS (Fm.D x i) w τ)).1 H _ hg

theorem amplitude_bounds_uniform_gap : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 A C1 : ℝ, ∃ C C2 Ch thr : ℝ, 0 ≤ C ∧ 0 ≤ Ch ∧ ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cpr : ℝ, ∀ δ > 0, (OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlus.AmplitudeBoundsConjunction (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1 Cpr C C2 Ch δ) := by
  intro hM hH hB Cg cb Cu cT CT C0 A C1
  obtain ⟨CPT, t1, hPT⟩ := GlobalTheory.T.uniform_amplitude_bound_wide_range_large_gap hM hH hB Cg cb Cu cT CT C0 C1
  obtain ⟨CDl, t2, hDl⟩ := GlobalTheory.FamDlGap.ptDl_along_family_gap hM hH hB Cg cb Cu cT CT C0 C1
  obtain ⟨t3, h5⟩ := GlobalTheory.CritLevelGap.tcritLow_along_family_gap hM hH hB Cg cb Cu cT CT C0
  obtain ⟨t4, h9⟩ := GlobalTheory.AmpFamGap.amplitudeNormDegree_along_family_largeGaps hM hH hB Cg cb Cu cT CT C0 C1
  obtain ⟨hilbertNinetyConstant, t5, hilbertNinetyConstant_pos, hDeg⟩ := GlobalTheory.DegStepG.degI_along_family hM hH hB Cg cb Cu cT CT C0 C1
  obtain ⟨Ca, t6, hCa, hAC⟩ := GlobalTheory.GapUAmp.abs_all_along_family_gap hM hH hB Cg cb Cu cT CT C0 A C1
  obtain ⟨CS, t8, hS⟩ := GlobalTheory.GapAmp.schur_along_family hM hH hB Cg cb Cu cT CT C0 C1
  obtain ⟨C, C2, Ch, hC, hCh, H⟩ := GlobalTheory.ampBounds_uniform_of_inputs Cg cb Cu cT CT C0 A C1 CPT CDl hilbertNinetyConstant Ca CS hilbertNinetyConstant_pos hCa
  refine ⟨C, C2, Ch, max t1 (max t2 (max t3 (max t4 (max t5 (max t6 t8))))), hC, hCh, ?_⟩
  intro eps Fm h1 h2 hR Cpr δ hδ
  exact H eps Fm
    (hPT eps Fm ((le_max_left _ _).trans h1) ((le_max_left _ _).trans h2) hR)
    (hDl eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR)
    (h5 eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR)
    (h9 eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR)
    (hDeg eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR)
    (hAC eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR).1
    (hAC eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR).2
    (hS eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR)
    (weyl_fam_gap eps Fm) Cpr δ hδ

end GlobalTheory.GapAmpUniform
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.row_doubleCoset_sum_norm_sq_bound : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ ν, Formalism.L2.SG.RealObj.NuQPin X u u' ν → ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → t₀.relevant → Formalism.L2.SG.PairVal.ptOf t₀.toTerm = w → ∀ Q : Prop → Prop, ‖∑' t : TauC Y u u', {t : TauC Y u u' | (Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ ∧ nmlOf Y u u' t = nmlOf Y u u' t₀ ∧ Q (¬ t.generic)}.indicator (Y.tO u u').vec t‖ ^ 2 = Formalism.L2.SG.TermOp.wt t₀ ^ 2 * ‖G.amp (G.datOf (c.lat ρ t₀.lam)) (fun Γ => Q (¬ G.Gen (G.datOf (c.lat ρ t₀.lam)) Γ))‖ ^ 2 * ((((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹) ^ 2 * ‖Formalism.L2.SG.PackageTie.hsEmb (Jw Y u u' ν w)‖ ^ 2) := by
  first | exact @GlobalTheory.HL.RowCoset.row_coset_sum_norm_sq | exact GlobalTheory.HL.RowCoset.row_coset_sum_norm_sq | (intros; apply GlobalTheory.HL.RowCoset.row_coset_sum_norm_sq <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs Formalism.FourierDecayAlt GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rowWeights_localOrbits_sum_eq_genusMass : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ {Cl : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl) (Fm : LocFam (zOf Y) Cl (NuC D)), Based (zOf Y) Fm.FP (Tu D u) (Tu D u') F F' → ClsRow TS cls → LocClosed F F' (zOf Y) Fm.FP TS → (∀ p ∈ Fm.P, ∀ d ∈ Fm.Ds p, d ∈ (Fm.R p).RD) → (∀ p, p ∉ Fm.P → ∀ t ∈ TS, ptPN t = toPts w → OverOrb Fm t p (Fm.d0 p)) → (∃ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ ∧ ∀ p, p ∉ Fm.P → ∃ τ, LocNG.IsTermOver (Fm.FP p) (Fm.d0 p) τ ∧ τ.abelian₂ = lattice₂ D (zOf Y).M p Λ₀) → (∀ c ν, (Fm.dat c ν = none → ¬ ∃ t ∈ TS, cls t = c ∧ ptPN t = toPts w ∧ nmlOf Y u u' t = ν) ∧ ∀ d, Fm.dat c ν = some d → (∃ t ∈ TS, cls t = c ∧ ptPN t = toPts w ∧ nmlOf Y u u' t = ν) ∧ ∀ t ∈ TS, cls t = c → ptPN t = toPts w → nmlOf Y u u' t = ν → (∀ p (hp : p ∈ Fm.P), OverOrb Fm t p (d ⟨p, hp⟩).1) ∧ Fm.rw c = (wt t) ^ 2) → ∀ d : (∀ p : {p // p ∈ Fm.P}, {d // d ∈ Fm.Ds p.1}), (∃ x : Cl × NuC D, Fm.dat x.1 x.2 = some d) → ∀ dd : Dat (zOf Y) Fm.FP, (∀ p (hp : p ∈ Fm.P), dd p = (d ⟨p, hp⟩).1) → (∀ p, p ∉ Fm.P → dd p = Fm.d0 p) → (∀ p, ∃ τ, LocNG.IsTermOver (Fm.FP p) (dd p) τ) ∧ ∑' x : {x : Cl × NuC D // Fm.dat x.1 x.2 = some d}, ENNReal.ofReal (Fm.rw x.1.1) = massA F F' dd := by
  first | exact @GlobalTheory.Unfold.GenusRows.rows_mass_genus | exact GlobalTheory.Unfold.GenusRows.rows_mass_genus | (intros; apply GlobalTheory.Unfold.GenusRows.rows_mass_genus <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs
open scoped Classical

theorem _root_.GlobalTheory.T.exists_localObjectFamily_classesDetermineRows : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ {Cl : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl), (∀ t ∈ TS, t.G ≠ 0) → (∀ t ∈ TS, ∀ t' ∈ TS, cls t = cls t' → (Y.tO u u').rowOf t = (Y.tO u u').rowOf t') → ∀ t₀ ∈ TS, t₀.relevant → ∃ Fm : LocFam (zOf Y) Cl (NuC D), FamTie TS cls (nmlOf Y u u') (ptPN t₀) Fm ∧ (∀ p ∈ Fm.P, (Fm.FP p).RelG (LocNG.theta ((zOf Y).M p))) ∧ (∀ p ∈ Fm.P, ∃ (d : LocNG.Datum (Fm.FP p)) (t : Loc.Term (Vp D p) ((zOf Y).M p) D.R.rS), LocNG.IsTermOver (Fm.FP p) d t) ∧ (∀ p ∈ Fm.P, ∀ d ∈ Fm.Ds p, d ∈ (Fm.R p).RD) ∧ (∀ c, 0 ≤ Fm.rw c) := by
  first | exact @GlobalTheory.FamGen.exists_famTie | exact GlobalTheory.FamGen.exists_famTie | (intros; apply GlobalTheory.FamGen.exists_famTie <;> assumption)
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AmplitudeConst

theorem normSq_inv_mul_sqrt (l d l' d' : ℝ) (hl : 0 < l) (hl' : 0 < l') (hd : 0 ≤ d) (hd' : 0 ≤ d') :
    Complex.normSq ((((l / d : ℝ) : ℂ))⁻¹ * ((Real.sqrt (l / d * d' / l') : ℝ) : ℂ)) = d / l * (d' / l') := by
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.normSq_ofReal]
  have hs : 0 ≤ l / d * d' / l' := by positivity
  have e : (l / d)⁻¹ * Real.sqrt (l / d * d' / l') * ((l / d)⁻¹ * Real.sqrt (l / d * d' / l')) =
      (l / d)⁻¹ * (l / d)⁻¹ * (Real.sqrt (l / d * d' / l') * Real.sqrt (l / d * d' / l')) := by ring
  rw [e, Real.mul_self_sqrt hs]
  rcases hd.eq_or_lt with h | h
  · subst h; simp
  · field_simp

theorem const_eq (P P' L L' K M H M' H' V V' : ℝ) (hK : 0 < K) (hM : 0 < M) (hH : 0 < H) (hM' : 0 < M')
    (hH' : 0 < H') (hL : 0 < L) (hL' : 0 < L') (hV : L * V = M * H) (hV' : L' * V' = M' * H')
    (hP : 0 ≤ P) (hP' : 0 ≤ P') :
    P / L * (P' / L') = ((Real.sqrt (K * M * H / P * (K * M' * H' / P')))⁻¹ * K) ^ 2 * (V * V') := by
  rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity), mul_inv, inv_div, inv_div]
  have eV : V = M * H / L := by field_simp; linarith
  have eV' : V' = M' * H' / L' := by field_simp; linarith
  subst eV eV'
  field_simp

theorem prod_finrank_loc {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    ∏ τ : D.what₂.Tau, (Module.finrank ℂ (X.Vloc u (vOf X τ)) : ℝ) = (Module.finrank ℂ (X.Vpi u) : ℝ) := by
  rw [Formalism.L2.SG.Pf.finrank_Vpi, Nat.cast_prod]
  exact Fintype.prod_equiv X.pl.symm _ _ fun τ => rfl

theorem prod_normSq_eq : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word), 0 < θ → Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∏ τ, Complex.normSq ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) = (Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2) ^ 2 * ((Measure.pi (fun _ : D.what₂.Tau => muNB D θ) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u)).toReal * (Measure.pi (fun _ : D.what₂.Tau => muNB D θ) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u')).toReal) := by
  intro D X Y hF θ C hB u u' hθ hG
  have hK0 : 0 ≤ X.volK2 := ENNReal.toReal_nonneg
  have hv := hF.volPos u
  have hv' := hF.volPos u'
  have hN : 0 < X.volK2 * (X.muN u (Y.FN u)).toReal := hv.1
  have hN' : 0 < X.volK2 * (X.muN u' (Y.FN u')).toReal := hv'.1
  have hK : 0 < X.volK2 := pos_of_mul_pos_left hN ENNReal.toReal_nonneg
  have hNu : 0 < (X.muN u (Y.FN u)).toReal := pos_of_mul_pos_right hN hK0
  have hNu' : 0 < (X.muN u' (Y.FN u')).toReal := pos_of_mul_pos_right hN' hK0
  have hHu : 0 < (X.muH u Set.univ).toReal := hv.2
  have hHu' : 0 < (X.muH u' Set.univ).toReal := hv'.2
  obtain ⟨hl, hp⟩ := GlobalTheory.T.product_l2_positive D X Y θ C hB u hθ hG hNu hHu
  obtain ⟨hl', hp'⟩ := GlobalTheory.T.product_l2_positive D X Y θ C hB u' hθ hG hNu' hHu'
  have hτ : ∀ τ, Complex.normSq ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) =
      (Module.finrank ℂ (X.Vloc u (vOf X τ)) : ℝ) / (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal *
        ((Module.finrank ℂ (X.Vloc u' (vOf X τ)) : ℝ) / (l2SG (C.nuS u' τ) (phiOf hB u' τ)).toReal) := by
    intro τ
    unfold sclOf cOf
    exact normSq_inv_mul_sqrt _ _ _ _ (hl τ) (hl' τ) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [Finset.prod_congr rfl fun τ _ => hτ τ, Finset.prod_mul_distrib, Finset.prod_div_distrib,
    Finset.prod_div_distrib, prod_finrank_loc, prod_finrank_loc]
  unfold Formalism.L2.SG.TermOp.scl Formalism.L2.SG.PoincareInHH.PoincareSetting.c0X
  exact const_eq _ _ _ _ _ _ _ _ _ _ _ hK hNu hHu hNu' hHu' (Finset.prod_pos fun τ _ => hl τ)
    (Finset.prod_pos fun τ _ => hl' τ) hp hp' (Nat.cast_nonneg _) (Nat.cast_nonneg _)

end GlobalTheory.AmplitudeConst
end
end
