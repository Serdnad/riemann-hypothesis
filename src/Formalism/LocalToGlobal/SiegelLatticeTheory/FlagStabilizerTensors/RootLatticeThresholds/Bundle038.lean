module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypOf
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle010
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SiegelMassRatioOfLI
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CriticalLevelLowOfRefined
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyCriticalLevelLowerBound
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle004
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle023
public import Formalism.PeriodIntegrals.Bundle004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.QuotMeasExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle031
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle032
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle036
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselFrame
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.MaximalCompactIsCompact
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppRedW
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle035
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictRing
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving

@[expose] public section

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Finset

namespace Formalism.L2.SG.Pf.SzHypFam


variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] in
theorem midVolumeChain_of_standingHypotheses {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT ep0 CV : ℝ} (hT : Ties D)
    (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (hCL : 1 ≤ Cl * large₂.sc.L) (he : 0 ≤ ep0) (hCV : 0 ≤ CV) :
    LocalBesselAndTopKernel.MidVolumeChain D large₂ ep0 CV := by
  intro τ
  rw [Formalism.L2.SG.Pf.SzHypFD.vv_eq_vand hT hH hCL τ]
  have h0 : 0 ≤ vand (lamSH D.R (D.hc τ)) := Formalism.MainNotions.BridgeLemma.szh_vand_nonneg _ (Formalism.MainNotions.BridgeLemma.szh_anti hH τ)
  have hL := Formalism.MainNotions.BridgeLemma.one_le_L large₂
  have hx : 0 ≤ CV * D.R.k * D.R.m * large₂.sc.L := by positivity
  have h1 : 1 ≤ Real.exp (CV * D.R.k * D.R.m * large₂.sc.L) := Real.one_le_exp hx
  constructor
  · nlinarith
  · nlinarith


variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] in
theorem familyTopBound_of_one_le_sCl {eps : ℝ} (Fm : FamP eps) (h1 : 1 ≤ sCl Fm) (C0 Cg cb Cu cT CT ep0 CV : ℝ) (he : 0 ≤ ep0)
    (hCV : 0 ≤ CV) : LocalBesselAndTopKernel.FamilyTopBound Fm C0 Cg cb Cu cT CT ep0 CV := by
  refine ⟨0, fun x _ i hh => ?_⟩
  have hL := Formalism.MainNotions.BridgeLemma.one_le_L (Fm.L x i)
  exact midVolumeChain_of_standingHypotheses (Fm.ties x i) hh.2.1 (by nlinarith) he hCV


variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] in
theorem localSplitExponents_of_forty_le_sCl {eps : ℝ} (Fm : FamP eps) (h40 : 40 ≤ sCl Fm) (C0 Cg cb Cu cT CT : ℝ) :
    LocalBesselAndTopKernel.LocalSplitExponents Fm C0 Cg cb Cu cT CT 1 :=
  Formalism.MainNotions.BridgeLemma.family_critical_level_lower_bound Fm (ep0 := 1 / 3) (CV := 0) h40 (by norm_num) le_rfl
    (familyTopBound_of_one_le_sCl Fm (by linarith) C0 Cg cb Cu cT CT (1 / 3) 0 (by norm_num) le_rfl)


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem secondSizeStatement_of_famP {eps : ℝ} (Fm : FamP eps) : LocalBesselAndTopKernel.SecondSizeStatement Fm := fun x i =>
  Formalism.MainNotions.BridgeLemma.mass_ratio_of_siegel_cm_unramified Formalism.HermitianLattices.Ext.L3.siegelMassRatio (Fm.D x i)


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem familyBesselBoundFirstPart_of_ranksF {eps : ℝ} (Fm : FamP eps) {C0 Cg cb Cu cT CT : ℝ} (hR : PX.RanksF Fm C0 Cg cb Cu cT CT) :
    LocalBesselAndTopKernel.FamilyBesselBoundFirstPart Fm C0 Cg cb Cu cT CT :=
  Formalism.MainNotions.BridgeLemma.level_formula_family Fm C0 Cg cb Cu cT CT (secondSizeStatement_of_famP Fm)
    (Formalism.MainNotions.BridgeLemma.mass_two_bound_family_holds Fm) hR


variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem tFrame_of_ranks {eps : ℝ} (Fm : FamP eps) (h40 : 40 ≤ sCl Fm) {C0 Cg cb Cu cT CT : ℝ}
    (hR : PX.RanksF Fm C0 Cg cb Cu cT CT) : PX.TFrame Fm Cg cb Cu cT CT C0 :=
  Formalism.MainNotions.BridgeLemma.level_frame_of_sizes Fm Cg cb Cu cT CT C0 1 (by linarith) (familyBesselBoundFirstPart_of_ranksF Fm hR)
    (localSplitExponents_of_forty_le_sCl Fm h40 C0 Cg cb Cu cT CT)

def aSz (C0 : ℝ) : List ℝ → ℝ := fun _ => Real.exp (3 / 4) * (C0 * Real.exp 1)

theorem one_le_aSz {C0 : ℝ} (h1 : 1 ≤ C0) (l : List ℝ) : 1 ≤ aSz C0 l := by
  unfold aSz
  have a := Real.one_le_exp (show (0 : ℝ) ≤ 3 / 4 by norm_num)
  have b := Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)
  have c : 1 ≤ C0 * Real.exp 1 := by nlinarith
  nlinarith


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem sizes3b_of_ranks {eps : ℝ} (Fm : FamP eps) (h40 : 40 ≤ sCl Fm) {C0 Cg cb Cu cT CT : ℝ} (h1 : 1 ≤ C0)
    (hR : PX.RanksF Fm C0 Cg cb Cu cT CT) :
    OwnEv Fm fun C' Cl x i => LocalBesselAndTopKernel.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl Cg cb Cu cT CT →
      Formalism.MainNotions.Sizes3b (Fm.D x i) (aSz C0 Fm.cOut) := by
  have hb : LocalBesselAndTopKernel.TheoremThreePassage Fm C0 Cg cb Cu cT CT (Real.exp (3 / 4)) := Formalism.MainNotions.BridgeLemma.family_critical_level_ratio Fm h40 le_rfl
  have hc : LocalBesselAndTopKernel.FamilyLowestKType Fm C0 Cg cb Cu cT CT (Real.exp (3 / 4) * (C0 * Real.exp 1)) :=
    Formalism.MainNotions.BridgeLemma.family_level_ratio_bound Fm C0 Cg cb Cu cT CT _ _ le_rfl (familyBesselBoundFirstPart_of_ranksF Fm hR) hb
  have hA := one_le_aSz h1 Fm.cOut
  have hC1 : Real.exp (3 / 4) ≤ aSz C0 Fm.cOut := by
    unfold aSz
    have b := Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)
    have c : 1 ≤ C0 * Real.exp 1 := by nlinarith
    have := Real.exp_pos (3 / 4)
    nlinarith
  exact Formalism.MainNotions.sizes3bF Fm C0 Cg cb Cu cT CT _ _ _ (Real.exp_pos _).le hC1 le_rfl hb hc


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] in
theorem szRowsAt_of_ties {D : D7} {large₂ : SizeData₂ D} {C0 C' Cl Cg cb Cu cT CT : ℝ} (hT : Ties D) (hD : StandingNumericalData D C0)
    (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (hCL : 1 ≤ Cl * large₂.sc.L) (hR : LocalBesselAndTopKernel.FamilyMidVolume D) :
    Formalism.L2.SG.Pf.SzHypOf.SzRowsAt D :=
  ⟨Formalism.MainNotions.BridgeLemma.mass_ratio_of_siegel_cm_unramified Formalism.HermitianLattices.Ext.L3.siegelMassRatio D, hR, Formalism.MainNotions.BridgeLemma.sza_spl_of_data hD,
    fun τ => Formalism.L2.SG.Pf.SzHypFD.fdl_of_ties hT hH hCL τ⟩

section Rows

open Formalism.L2.SG.ThmSOwn

variable (C0 : ℝ)

def RanksRow (𝒞 : FamClass) : Prop :=
  Closed 𝒞 fun Fm _ => PX.RanksF Fm C0 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu


variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem hTF_of_ranks {𝒞 : FamClass} (hRk : RanksRow C0 𝒞) :
    Closed 𝒞 fun Fm _ => PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 :=
  closed_with hRk (fun _ => 0) (fun _ => 40) fun Fm _ _ hR _ _ h2 => tFrame_of_ranks Fm h2 hR


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem hA_of_ranks {𝒞 : FamClass} (h1 : 1 ≤ C0) (hRk : RanksRow C0 𝒞) :
    Closed 𝒞 fun Fm _ => 1 ≤ aSz C0 Fm.cOut ∧ OwnEv Fm fun C' Cl x i =>
      AdmissibleBoundsFromSource.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu →
        Formalism.MainNotions.Sizes3b (Fm.D x i) (aSz C0 Fm.cOut) :=
  closed_with hRk (fun _ => 0) (fun _ => 40) fun Fm _ _ hR _ _ h2 =>
    ⟨one_le_aSz h1 _, sizes3b_of_ranks Fm h2 h1 hR⟩


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] in
theorem hRw_of_ranks {𝒞 : FamClass} (hRk : RanksRow C0 𝒞) :
    Closed 𝒞 fun Fm _ => OwnEv Fm fun C' Cl x i =>
      AdmissibleBoundsFromSource.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu →
        Formalism.L2.SG.Pf.SzHypOf.SzRowsAt (Fm.D x i) :=
  closed_with hRk (fun _ => 0) (fun _ => 1) fun Fm _ _ hR _ _ h2 => by
    obtain ⟨x0, H⟩ := hR
    refine ⟨x0, fun x hx i hh => ?_⟩
    have hL := Formalism.MainNotions.BridgeLemma.one_le_L (Fm.L x i)
    have h2' : 1 ≤ sCl Fm := h2
    exact szRowsAt_of_ties (Fm.ties x i) hh.1 hh.2.1 (by nlinarith) (H x hx i hh)

end Rows

end Formalism.L2.SG.Pf.SzHypFam
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf
open scoped ENNReal

namespace Formalism.L2.SG.Pf.RMeasP

theorem rset_matGroup {k r : ℕ} {g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hu : IsUnit g₀.det) :
    PI.IsMatGroup (Formalism.MainNotions.S.Rset k r g₀) := by
  have hui : IsUnit (g₀⁻¹).det := Matrix.isUnit_nonsing_inv_det g₀ hu
  have hc := Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR (k := k) (r := r) hui
  have hset : Formalism.FourierDecayAlt.C6.Rset g₀⁻¹ = Formalism.MainNotions.S.Rset k r g₀ := by
    ext x
    simp only [Formalism.FourierDecayAlt.C6.Rset, Formalism.MainNotions.S.Rset, Set.mem_ofPred_eq, Matrix.nonsing_inv_nonsing_inv _ hu]
  rw [← hset]
  exact ⟨hc.closed, hc.one_mem, hc.mul_mem, fun a ha => ⟨hc.inv_mem a ha, Matrix.mul_nonsing_inv a (hc.unit a ha)⟩⟩

theorem isHaarOn_smul' {k r : ℕ} {S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)} {μ : Measure (Mt k r)}
    (h : Formalism.MainNotions.S.IsHaarOn S μ) {c : ℝ≥0∞} (h0 : c ≠ 0) (h1 : c ≠ ⊤) : Formalism.MainNotions.S.IsHaarOn S (c • μ) := by
  unfold Formalism.MainNotions.S.IsHaarOn at h ⊢
  obtain ⟨hs, hne, hnull, hinv⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · first
      | infer_instance
      | (rw [← ENNReal.coe_toNNReal h1, ← ENNReal.smul_def]; infer_instance)
  · first
      | exact smul_ne_zero h0 hne
      | (intro hz
         apply hne
         have hu := congrArg (fun ν : Measure (Mt k r) => ν Set.univ) hz
         simp [h0] at hu
         first
           | exact hu
           | exact Measure.measure_univ_eq_zero.mp hu)
  · rw [Measure.smul_apply, hnull, smul_zero]
  · intro s hs'
    rw [Measure.map_smul, hinv s hs']
    exact (Formalism.L2.SG.Pf.WFL.measurable_lmulM s).aemeasurable

theorem rMeas_exact (D : D7) (W : LocW D.R.k D.R.rS) (hz : inWb D.R.k D.R.rS W.z) (hT : 0 < Tz D.R.k D.R.rS W.z)
    (hz' : inWb D.R.k D.R.rS W.z') (hT' : 0 < Tz D.R.k D.R.rS W.z')
    (hG : Formalism.MainNotions.S.IsHaarOn (UH (Hpk D.R.k D.R.rS)) W.μG) (p : Point ℂ (D.R.rS + 1)) (g₀ : MatKR D.R.k D.R.rS)
    (hg : g₀ ∈ UH (Hpk D.R.k D.R.rS)) (hZ : Formalism.MainNotions.S.ZhatO D.R.k D.R.rS W.z W.z' g₀ = ptMat p) :
    ∃ ν, RMeas D W g₀ 1 ν := by
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  obtain ⟨μ₀', c, hH, hc0, hc1, hmap⟩ :=
    Formalism.L2.SG.Pf.RootHaarLoc.locRootHaar D.R.k D.R.rS hk W.z W.z' hz hT hz' hT' p g₀ hg hZ
  set K : ℝ≥0∞ := ENNReal.ofReal ((2 * D.host.ka / gg D / (2 * Real.pi)) ^ (rootPat p).card) with hK
  have hu : IsUnit g₀.det := (Formalism.FourierDecayAlt.P.unitary_group_closed D.R.k D.R.rS).unit g₀ hg
  by_cases hK0 : K = 0
  ·

    exfalso
    have hka : 0 < 2 * D.host.ka / gg D / (2 * Real.pi) := by
      have h1 : 0 < D.host.ka := by
        unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v Formalism.BasicNotions.Host.rdE
        have h : (0 : ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
          abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
        have := Real.rpow_pos_of_pos h ((1 : ℝ) / (Module.finrank ℚ D.host.E : ℝ))
        positivity
      have h2 : 0 < gg D := by
        unfold gg
        have a := (D.host.g_prime 0).pos
        have b := (D.host.g_prime 1).pos
        positivity
      positivity
    rw [hK, ENNReal.ofReal_eq_zero] at hK0
    exact absurd hK0 (not_le.2 (pow_pos hka _))
  have hKt : K ≠ ⊤ := ENNReal.ofReal_ne_top
  set μ₀ : Measure (Mt D.R.k D.R.rS) := (K * c⁻¹) • μ₀' with hμ₀
  have hKc0 : K * c⁻¹ ≠ 0 := mul_ne_zero hK0 (ENNReal.inv_ne_zero.2 hc1)
  have hKc1 : K * c⁻¹ ≠ ⊤ := ENNReal.mul_ne_top hKt (ENNReal.inv_ne_top.2 hc0)
  have hH0 : Formalism.MainNotions.S.IsHaarOn (Formalism.MainNotions.S.Rset D.R.k D.R.rS g₀) μ₀ := isHaarOn_smul' hH hKc0 hKc1
  have hmap0 : μ₀.map (rootCoords D.R.k D.R.rS W.z' p) = K • volume := by
    rw [hμ₀, Measure.map_smul, hmap, smul_smul, mul_assoc, ENNReal.inv_mul_cancel hc0 hc1, mul_one]
    apply Continuous.aemeasurable
    unfold Formalism.MainNotions.S.rootCoords
    refine continuous_pi (fun q => ?_)
    unfold flagMat
    by_cases hi : q.1.1.val < D.R.rS
    · simp only [hi, ↓reduceDIte]
      fun_prop
    · simp only [hi, ↓reduceDIte]
      exact continuous_const
  have hid : μ₀.map (fun x => fun i j => ((1 : MatKR D.R.k D.R.rS)⁻¹ * Matrix.of x * 1) i j) = μ₀ := by
    have : (fun x : Mt D.R.k D.R.rS => fun i j => ((1 : MatKR D.R.k D.R.rS)⁻¹ * Matrix.of x * 1) i j) = id := by
      funext x i j
      simp
    rw [this, Measure.map_id]
  have hN1 : (1 : MatKR D.R.k D.R.rS) ∈ Nset D.R.k D.R.rS := (Formalism.FourierDecayAlt.P.unipotent_radical_closed D.R.k D.R.rS).one_mem
  have hsub : Formalism.MainNotions.S.Rset D.R.k D.R.rS g₀ ⊆ UH (Hpk D.R.k D.R.rS) := fun x hx => hx.1.1
  obtain ⟨ν, hν⟩ := Formalism.L2.SG.Pf.QuotMeasExists.quotM_exists (PI.QuotSetU.UnitaryGroupMassFormula.unitary_hermitian_group D.R.k D.R.rS)
    (rset_matGroup hu) hsub hG hH0
  refine ⟨ν, p, μ₀, ⟨1, hN1, 1, hN1, g₀, by simp, hZ, μ₀, hH0.2.2.1, ?_, hid.symm⟩, ?_⟩
  · rw [hmap0]
  · rw [ENNReal.ofReal_one, one_smul]
    exact hν

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (u u' : D.what₂.Word)

theorem rMeasExP_of_goodW (hW : ∀ τ, GoodW D τ u u' θ (locW C u u' τ)) : Formalism.L2.SG.Pf.JointAmplitudePoints.RMeasExP u u' C := by
  intro w _ hrep τ
  obtain ⟨_, _, h3, h4, h5, h6, h7, _⟩ := hW τ
  have hTu : 0 < Tr D u := Nat.cast_pos.2 (D.mem u).A.T_prime.pos
  have hTu' : 0 < Tr D u' := Nat.cast_pos.2 (D.mem u').A.T_prime.pos
  exact rMeas_exact D (locW C u u' τ) h3 (by rw [h5]; exact hTu) h4 (by rw [h6]; exact hTu') h7
    (ptLoc D τ w) (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' w τ)
    (Formalism.L2.SG.Pf.LTL.trG_mem _ _ _ (C.isT τ).2.1 (C.isT τ).2.2.1 _)
    (Formalism.L2.SG.Pf.RelPtR.zhatO_gamP C u u' w hrep τ)

end Formalism.L2.SG.Pf.RMeasP
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppChar

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowDictPf Formalism.L2.SG.Pf.AllRowsRedKerA
  Formalism.L2.SG.Pf.AllRowsRedKer Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.RedBasicsPf

variable {D : D7} (X : HidaSetting D)

theorem Wq_of_congW_zero {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) {t : I.E ⊗[I.F] Af I.F} (h : CongW (w := w) p t 0) : t ∈ Wq I w := by
  obtain ⟨c, hc, ht⟩ := h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hc
  obtain ⟨q, rfl⟩ := hc
  have : ((((p : ℤ) * q : ℤ)) : I.E ⊗[I.F] Af I.F) ∈ Wq I w := by
    push_cast
    exact Wq_mul' (natCast_Wq hp hcard) (intCast_mem _ q)
  have := add_mem ht this
  simpa using this

theorem psi_sum {ι : Type*} (s : Finset ι) (f : ι → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :
    X.psiEf (divN X.B.I X.B.g (∑ i ∈ s, f i)) = ∏ i ∈ s, X.psiEf (divN X.B.I X.B.g (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty]
    unfold divN; rw [mul_zero]; exact X.psiEf_int 0 (zero_mem _)
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, divN_add, X.psiEf_add, ih]

theorem congW_iE {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {p : ℕ} {a : 𝓞 I.E} {m : ℤ}
    (h : a - (m : 𝓞 I.E) ∈ w.asIdeal) : CongW (w := w) p (iE I a) (m : ZMod p) := by
  refine ⟨m, rfl, ?_⟩
  have := iE_mem (I := I) h
  simpa [iE] using this

variable (ε : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), 𝓞 X.B.I.E)

theorem chi_split (hε1 : ∀ kv, ε kv - 1 ∈ (wK X kv).asIdeal)
    (hεP : ∀ kv (P : HeightOneSpectrum (𝓞 X.B.I.E)), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → P ≠ wK X kv →
      ε kv ∈ P.asIdeal)
    (hε : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ε kv ∈ Ideal.span {((D.host.g (1 - kv.1) : ℕ) : 𝓞 X.B.I.E)})
    (hn : 0 < X.B.I.n) {C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hC : C ∈ IntAf X.B.I.F X.B.I.E)
    (t1 t2 : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1))
    (h1 : ∀ kv, CongW (w := wK X kv) (D.host.g kv.1) C (t1 kv))
    (h2 : ∀ kv, CongW (w := wc X.B.I (wK X kv)) (D.host.g kv.1) C (t2 kv)) :
    X.psiEf (divN X.B.I X.B.g C) = ∏ kv, psiK X (ε kv) (hε kv) (t1 kv + t2 kv) := by
  classical
  set T : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F := ∑ kv, (iE X.B.I (ε kv) * (((t1 kv).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) +
    iE X.B.I (sigO X.B.I (ε kv)) * (((t2 kv).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) with hT
  have hTint : T ∈ IntAf X.B.I.F X.B.I.E :=
    sum_mem fun kv _ => add_mem (mul_mem (iE_int _ _) (natCast_mem _ _)) (mul_mem (iE_int _ _) (natCast_mem _ _))

  have hgP : ∀ kv, ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal := fun kv => level_mem_wB' X kv
  have hgPc : ∀ kv, ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ (wc X.B.I (wK X kv)).asIdeal :=
    fun kv => natCast_mem_wc X.B.I (level_mem_wB' X kv)
  have hΔ : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → C - T ∈ Wq X.B.I P := by
    intro P hP
    obtain ⟨kv0, hP0 | hP0⟩ := over_g X P hP
    · subst hP0
      have hp := D.host.g_prime kv0.1
      have : NeZero (D.host.g kv0.1) := ⟨hp.ne_zero⟩
      have hTc : CongW (w := wK X kv0) (D.host.g kv0.1) T (t1 kv0) := by
        have h3 : CongW (w := wK X kv0) (D.host.g kv0.1) T
            (∑ kv, ((if kv = kv0 then 1 else 0) * (((t1 kv).val : ℕ) : ZMod (D.host.g kv0.1)) +
              0 * (((t2 kv).val : ℕ) : ZMod (D.host.g kv0.1)))) := by
          refine congW_sum _ fun kv _ => congW_add ?_ ?_
          · refine congW_mul (natCast_mem _ _) ?_ (congW_natCast _)
            by_cases hk : kv = kv0
            · subst hk
              rw [if_pos rfl]
              have := congW_iE (p := D.host.g kv.1) (m := 1) (by simpa using hε1 kv)
              simpa using this
            · rw [if_neg hk]
              have := congW_iE (p := D.host.g kv0.1) (m := 0)
                (by simpa using hεP kv (wK X kv0) (hgP kv0) (wK_ne X (Ne.symm hk)))
              simpa using this
          · refine congW_mul (natCast_mem _ _) ?_ (congW_natCast _)
            have hm : ε kv ∈ (wc X.B.I (wK X kv0)).asIdeal := hεP kv _ (hgPc kv0) (wK_ne_wc X kv kv0).symm
            rw [mem_wc] at hm
            have := congW_iE (p := D.host.g kv0.1) (m := 0) (by simpa using hm)
            simpa using this
        convert h3 using 1
        simp [Finset.sum_ite_eq']
      have := congW_sub (h1 kv0) hTc
      rw [sub_self] at this
      exact Wq_of_congW_zero hp (card_wK X kv0) this
    · subst hP0
      have hp := D.host.g_prime kv0.1
      have : NeZero (D.host.g kv0.1) := ⟨hp.ne_zero⟩
      have hTc : CongW (w := wc X.B.I (wK X kv0)) (D.host.g kv0.1) T (t2 kv0) := by
        have h3 : CongW (w := wc X.B.I (wK X kv0)) (D.host.g kv0.1) T
            (∑ kv, (0 * (((t1 kv).val : ℕ) : ZMod (D.host.g kv0.1)) +
              (if kv = kv0 then 1 else 0) * (((t2 kv).val : ℕ) : ZMod (D.host.g kv0.1)))) := by
          refine congW_sum _ fun kv _ => congW_add ?_ ?_
          · refine congW_mul (natCast_mem _ _) ?_ (congW_natCast _)
            have hm : ε kv ∈ (wc X.B.I (wK X kv0)).asIdeal := hεP kv _ (hgPc kv0) (wK_ne_wc X kv kv0).symm
            have := congW_iE (p := D.host.g kv0.1) (m := 0) (by simpa using hm)
            simpa using this
          · refine congW_mul (natCast_mem _ _) ?_ (congW_natCast _)
            by_cases hk : kv = kv0
            · subst hk
              rw [if_pos rfl]
              have hm : sigO X.B.I (ε kv) - 1 ∈ (wc X.B.I (wK X kv)).asIdeal := by
                rw [mem_wc, map_sub, sigO_sigO, map_one]; exact hε1 kv
              have := congW_iE (p := D.host.g kv.1) (m := 1) (by simpa using hm)
              simpa using this
            · rw [if_neg hk]
              have hm : sigO X.B.I (ε kv) ∈ (wc X.B.I (wK X kv0)).asIdeal := by
                rw [mem_wc, sigO_sigO]; exact hεP kv (wK X kv0) (hgP kv0) (wK_ne X (Ne.symm hk))
              have := congW_iE (p := D.host.g kv0.1) (m := 0) (by simpa using hm)
              simpa using this
        convert h3 using 1
        simp [Finset.sum_ite_eq']
      have := congW_sub (h2 kv0) hTc
      rw [sub_self] at this
      exact Wq_of_congW_zero hp (card_wKc X kv0) this

  obtain ⟨a, r', hr', hr⟩ := PIW.AdelClassFin.dual_dense X.B.I.F X.B.I.E X.B.g (g_pos X) (C - T) (sub_mem hC hTint)
  have ha : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → a ∈ P.asIdeal := by
    intro P hP
    have hgW : (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ Wq X.B.I P := by
      have := iE_mem (I := X.B.I) hP; simpa [iE] using this
    have hiE : iE X.B.I a ∈ Wq X.B.I P := by
      have := sub_mem (hΔ P hP) (Wq_mul' hgW hr')
      rw [hr] at this
      simpa [iE] using this
    obtain ⟨kv0, hP0 | hP0⟩ := over_g X P hP
    · subst hP0; exact int_of_Wq (D.host.g_prime kv0.1) (card_wK X kv0) hn hiE
    · subst hP0; exact int_of_Wq (D.host.g_prime kv0.1) (card_wKc X kv0) hn hiE
  obtain ⟨c, hc⟩ := mem_g_of_all X ha
  have hCT : C = T + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (iE X.B.I c + r') := by
    have : C - T = (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (iE X.B.I c + r') := by
      rw [hr, hc]; simp [iE]; ring
    rw [← this]; ring
  rw [hCT, psi_modg X _ (add_mem (iE_int _ c) hr'), hT, psi_sum]
  refine Finset.prod_congr rfl fun kv _ => ?_
  rw [divN_add, X.psiEf_add, psi_sig, AddChar.map_add_eq_mul, psiK_apply, psiK_apply]

end Formalism.L2.SG.Pf.KppChar
end
end
