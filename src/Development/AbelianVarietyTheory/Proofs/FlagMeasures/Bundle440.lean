module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle021
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle018
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle310
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle256
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle361
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle368
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle357
public import Formalism.HermitianCurvature.Bundle008
public import Formalism.HermitianCurvature.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeSumOfCompactCoefficientPositivity
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle060
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle078
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle438
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EquivPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle057
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocJEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle056
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BlockGrp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstGVol
public import Formalism.UnipotentAdelicQuotients.Bundle003
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle401
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle392
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle406
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle290
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle427
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle264
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle391
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle439
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle342
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.CoefWeightedLocHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations

@[expose] public section

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.identificationCompat_passes_to_local_congruence : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), PD D Λ (lf D F0) u' F₁ → PD D Λ (lf D F0) u' F₂ → ∀ β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT, Formalism.HermitianLatticesTheory.gmap β Λ = Λ → (∀ a, frame F₂ a = β (frame F₁ a)) → IotaCompat Λ (lf D F0) F₁ F₂ β (gS D) → ∀ (p : PlF D) (g), Ext p β g → (Z.M p).split ≠ none → ∀ x' ∈ lattice₂ D Z.M p Λ, ∀ x ∈ lattice₂ D Z.M p Λ, x' ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame F₁))) → x ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame (lf D F0)))) → (Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame (lf D F0))) (scaled Z p (frame F₁)) (x - x') ↔ Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame (lf D F0))) (scaled Z p (frame F₂)) (x - g x')) := by
  first | exact @GlobalTheory.IotaLoc.iota_typed | exact GlobalTheory.IotaLoc.iota_typed | (intros; apply GlobalTheory.IotaLoc.iota_typed <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

theorem _root_.GlobalTheory.T.exists_maximalCompact_reduction_standardFrame : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E), StdPsi hF PY → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∃ c red, FrameRed X h t PY c red := by
  first | exact @GlobalTheory.LabPin.frameRed_exists | exact GlobalTheory.LabPin.frameRed_exists | (intros; apply GlobalTheory.LabPin.frameRed_exists <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

theorem _root_.GlobalTheory.T.oneBessel_torusTranslates_largeGap : GlobalTheory.GapIn.Hyp → ∃ Cgf : ℝ, ∀ D : D7, Formalism.MainNotions.FrameBoundFromBesselTorus.OneBesselTor D Cgf := by
  first | exact @GlobalTheory.AmpTKGapOne.oneBesselTor_of_gapHyp | exact GlobalTheory.AmpTKGapOne.oneBesselTor_of_gapHyp | (intros; apply GlobalTheory.AmpTKGapOne.oneBesselTor_of_gapHyp <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

namespace GlobalTheory.LoopVol

theorem pinned_ratCoord_le : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γw sf : X.B.I.Ginf) (μw : MeasureTheory.Measure X.B.I.Ginf), IsHaarOnSet X.B.I (Formalism.L2.SG.RealObj.StInf X u u' γw) μw → μw.map (Formalism.L2.SG.RealObj.stCoord X u' w γw) = Formalism.L2.SG.RealObj.muStab X w → D.host.ka / (X.B.g : ℝ) / Real.pi ≤ 1 → ∀ A : Set (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ), MeasurableSet A → (μw.map (fun y => sf * y * sf⁻¹)) (GlobalTheory.LoopVol.ratCoord X u' w γw sf ⁻¹' A) ≤ MeasureTheory.volume A * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) := by
  intro D X u u' w γw sf μw _hH hmap hc A hA
  classical

  let ι : GlobalTheory.LoopV.roots (ptMat w) ≃ Formalism.L2.SG.RealObj.FreeE w :=
    Equiv.subtypeEquivRight (fun p => GlobalTheory.T.mem_roots_point_matrix_iff_same_block D.host.E (D.R.rS + 1) w p.1 p.2)
  let d : GlobalTheory.LoopV.roots (ptMat w) → ℕ := fun q => q.1.2.1 - q.1.1.1
  let S : (NumberField.InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ) → (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ) :=
    fun x τ q => (((D.host.rdE : ℝ) : ℂ) ^ d q)⁻¹ * x (X.pl.symm τ) (ι q)
  have hS : Continuous S := by
    refine continuous_pi fun τ => continuous_pi fun q => continuous_const.mul ?_
    exact (continuous_apply _).comp (continuous_apply _)
  have hΦ : Continuous (fun y : X.B.I.Ginf => sf * y * sf⁻¹) :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hst := Formalism.L2.SG.Pf.LoopBPin.stCoord_cont (X := X) u' w γw
  have hrat := ratCoord_cont X u' w γw sf
  have hpre : (fun y : X.B.I.Ginf => sf * y * sf⁻¹) ⁻¹' (ratCoord X u' w γw sf ⁻¹' A) =
      Formalism.L2.SG.RealObj.stCoord X u' w γw ⁻¹' (S ⁻¹' A) := by
    ext y
    simp only [Set.mem_preimage]
    have : ratCoord X u' w γw sf (sf * y * sf⁻¹) = S (Formalism.L2.SG.RealObj.stCoord X u' w γw y) := by
      funext τ q
      exact ratCoord_conj_eq_stCoord D X u' w γw sf y τ q (ι q) rfl
    rw [this]
  have hB : MeasurableSet (S ⁻¹' A) := hS.measurable hA
  rw [Measure.map_apply hΦ.measurable (hrat.measurable hA), hpre,
    ← Measure.map_apply hst.measurable hB, hmap]
  have hrd : 1 ≤ D.host.rdE := GlobalTheory.RealPlaces.one_le_rdE (D := D)
  have key := GlobalTheory.T.measure_preimage_reindex_scale_complex_le D.what₂.Tau (NumberField.InfinitePlace X.B.I.F) (GlobalTheory.LoopV.roots (ptMat w)) (Formalism.L2.SG.RealObj.FreeE w)
    X.pl.symm ι D.host.rdE (D.host.ka / (X.B.g : ℝ) / Real.pi) d hrd hc A hA
  refine le_trans key ?_
  gcongr
  · rw [D.what₂.card_Tau]
  · have hsum : ∑ q : GlobalTheory.LoopV.roots (ptMat w), d q ≤ (D.R.rS + 1) ^ 3 := by
      calc ∑ q : GlobalTheory.LoopV.roots (ptMat w), d q ≤ ∑ _q : GlobalTheory.LoopV.roots (ptMat w), (D.R.rS + 1) :=
            Finset.sum_le_sum fun q _ => by
              have := q.1.2.2; simp only [d]; omega
        _ = Fintype.card (GlobalTheory.LoopV.roots (ptMat w)) * (D.R.rS + 1) := by simp
        _ ≤ (D.R.rS + 1) ^ 2 * (D.R.rS + 1) := by
            gcongr
            calc Fintype.card (GlobalTheory.LoopV.roots (ptMat w)) ≤ Fintype.card (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) :=
                  Fintype.card_subtype_le _
              _ = (D.R.rS + 1) ^ 2 := by simp [sq]
        _ = (D.R.rS + 1) ^ 3 := by ring
    exact hsum

end GlobalTheory.LoopVol
end

section

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

theorem _root_.GlobalTheory.T.latticeSum_of_compactCoefficient_positivity : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base G → (∀ y, 0 < nn y) → TBB.BlockGrowthBound p nn G Y K N := by
  first | exact @GlobalTheory.LatticeGerm.latticeSum_of_cptCoef | exact GlobalTheory.LatticeGerm.latticeSum_of_cptCoef | (intros; apply GlobalTheory.LatticeGerm.latticeSum_of_cptCoef <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna

theorem _root_.GlobalTheory.T.equalWords_nonGeneric_estimates_chain : PN.NGChain ∧ StepClassG ∧ StepPointsG ∧ StepNormOneG ∧ TieOfCtx ∧ StepPinExists ∧ StepTermVanishG ∧ Formalism.L2.SG.NGVanish.FormNGC ∧ (Formalism.L2.SG.Pf.MainEqFam.StepFamG → StepLocGenPinnedG) := by
  first | exact @GlobalTheory.closed_steps_equal_words | exact GlobalTheory.closed_steps_equal_words | (intros; apply GlobalTheory.closed_steps_equal_words <;> assumption)
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.transportedFundDomain_volume_classical : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), (Measure.pi (fun _ : D.what₂.Tau => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u)).toReal = (2 * D.host.v) ^ (((D.R.rS : ℝ) ^ 2 + (D.R.rS : ℝ) * D.R.k + (D.R.rS : ℝ) / 2) * Fintype.card D.what₂.Tau) := by
  first | exact @GlobalTheory.CovDom.main | exact GlobalTheory.CovDom.main | (intros; apply GlobalTheory.CovDom.main <;> assumption)
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SlocTie

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem uh_mul {k r : ℕ} {a b : MatKR k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hb : b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : a * b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
  show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [ha', hb']

theorem b_eq_wT (C : Choice X θ) (hB : WuBessel C) (u : D.what₂.Word) (τ : D.what₂.Tau) {m : MatKR D.R.k D.R.rS}
    (hm : m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    bOf hB u τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ)) = wT C u τ (m * C.y τ) := by
  have hmy : m * C.y τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := uh_mul hm (C.y_mem τ)
  have hJ := Formalism.L2.SG.Pf.LocJEq.transp_mem C τ hmy
  have hex : ∃ γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)), uMat γ = C.Q τ * (m * C.y τ) * C.Qi τ :=
    ⟨Formalism.L2.SG.Pf.LocJEq.ujOf' _ hJ, rfl⟩
  unfold wT
  rw [dite_eq_left hex, Formalism.L2.SG.Pf.LocJEq.wloc_eq C hB u τ]
  have hc : Formalism.MainNotions.S.umat hex.choose = C.Q τ * (m * C.y τ) * C.Qi τ := hex.choose_spec
  rw [hc]
  unfold v0Of sigB
  rw [← Formalism.L2.SG.Pf.LocJEq.sig_mul τ (Formalism.L2.SG.Pf.LocJEq.transp_mem C τ hm)
    (Formalism.L2.SG.Pf.LocJEq.transp_mem C τ (C.y_mem τ))]
  congr 2
  have e : C.Q τ * m * C.Qi τ * (C.Q τ * C.y τ * C.Qi τ) = C.Q τ * m * (C.Qi τ * C.Q τ) * C.y τ * C.Qi τ := by
    simp only [Matrix.mul_assoc]
  rw [e, (C.isT τ).1, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

end GlobalTheory.SlocTie

namespace GlobalTheory.SlocTie

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem isSPsiEquiv_transl {k r : ℕ} {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {ψ : MatKR k r → ℂ} {π : MatKR k r → (Wp →L[ℂ] Wp)} {W F : MatKR k r → Wp}
    {y : MatKR k r} (s : ℂ) (hy : y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hW : IsSPsiEquiv z ψ π W)
    (hF : ∀ m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), F m = s • W (m * y)) : IsSPsiEquiv z ψ π F := by
  intro h hh n hn g hg
  have hhng : h * n * g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := uh_mul (uh_mul hh.1 hn.1) hg
  rw [hF _ hhng, hF g hg, Matrix.mul_assoc (h * n) g y, hW h hh n hn (g * y) (uh_mul hg hy), map_smul,
    smul_comm s (ψ n)]

theorem continuousOn_transl {k r : ℕ} {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    {W F : MatKR k r → Wp} {y : MatKR k r} (s : ℂ) (hy : y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hW : ContinuousOn W (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)))
    (hF : ∀ m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), F m = s • W (m * y)) :
    ContinuousOn F (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
  have h1 : ContinuousOn (fun m : MatKR k r => s • W (m * y)) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :=
    (hW.comp (continuous_id.matrix_mul continuous_const).continuousOn fun m hm => uh_mul hm hy).const_smul s
  exact h1.congr hF

theorem phi_eq (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau) :
    ∀ m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS), (locS hB u u' τ).Φ m = (1 : ℂ) • wT C u τ (m * C.y τ) :=
  fun m hm => by rw [one_smul]; exact b_eq_wT C hB u τ hm

theorem phi'_eq (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau) :
    ∀ m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS),
      (locS hB u u' τ).Φ' m = sclOf hB u u' τ • wT C u' τ (m * C.y τ) :=
  fun m hm => by
    show sclOf hB u u' τ • bOf hB u' τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ)) = _
    rw [b_eq_wT C hB u' τ hm]

theorem tie_of (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hc : ∀ u, ContinuousOn (wT C u τ) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)))
    (he : ∀ u, IsSPsiEquiv (zB X (C.Qi τ) u τ) (psiS D (zB X (C.Qi τ) u τ)) (piB X (C.Q τ) (C.Qi τ) u τ) (wT C u τ)) :
    IsSPsiEquiv (locW C u u' τ).z (psiS D (locW C u u' τ).z) (locW C u u' τ).π (locS hB u u' τ).Φ ∧
    IsSPsiEquiv (locW C u u' τ).z' (psiS D (locW C u u' τ).z') (locW C u u' τ).π' (locS hB u u' τ).Φ' ∧
    ContinuousOn (locS hB u u' τ).Φ (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) ∧
    ContinuousOn (locS hB u u' τ).Φ' (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :=
  ⟨isSPsiEquiv_transl 1 (C.y_mem τ) (he u) (phi_eq C hB u u' τ),
    isSPsiEquiv_transl _ (C.y_mem τ) (he u') (phi'_eq C hB u u' τ),
    continuousOn_transl 1 (C.y_mem τ) (hc u) (phi_eq C hB u u' τ),
    continuousOn_transl _ (C.y_mem τ) (hc u') (phi'_eq C hB u u' τ)⟩

end GlobalTheory.SlocTie

namespace GlobalTheory.SlocTie

theorem locS_phi_equiv_cont : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C)
    (u u' : D.what₂.Word) (τ : D.what₂.Tau), Formalism.L2.SG.ConcreteSettingExists.GapHyp D →
    IsSPsiEquiv (locW C u u' τ).z (psiS D (locW C u u' τ).z) (locW C u u' τ).π (locS hB u u' τ).Φ ∧
    IsSPsiEquiv (locW C u u' τ).z' (psiS D (locW C u u' τ).z') (locW C u u' τ).π' (locS hB u u' τ).Φ' ∧
    ContinuousOn (locS hB u u' τ).Φ (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) ∧
    ContinuousOn (locS hB u u' τ).Φ' (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :=
  fun D X θ C hB u u' τ _ =>
    tie_of C hB u u' τ (fun u => Formalism.L2.SG.Pf.LocF.local_continuity_all D X θ C u τ)
      (fun u => Formalism.L2.SG.Pf.EquivPf.local_equivalence_all D X θ C u τ)

end GlobalTheory.SlocTie
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem pinAll_all : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), PinAll (Y := Y) u u' :=
  fun _ _ _ u u' => Formalism.L2.SG.Pf.LoopBPin.pinAll_holds u u'

end GlobalTheory
end

section

namespace GlobalTheory.GaugeVolumeUD

theorem gaugeVolUD : PI.AprimeInfW.GaugeVolUD := fun k => Formalism.L2.SG.Pf.GV.gaugeVolU k

instance : Fact (PI.AprimeInfW.GaugeVolUD) := ⟨gaugeVolUD⟩

end GlobalTheory.GaugeVolumeUD
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.ColDict

namespace GlobalTheory.St.SpectralData

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_transport {D : D7} (F : ∀ u, Formalism.L2.Forms.Forms0 D u)
    (X : HidaSetting D) (hK : X.LevelSubgroupCharacter) (hι : ∃ ιA, GlobalTheory.St.IsAdeleIso X ιA) (u : D.what₂.Word) :
    ∃ Tr : Transport X u (F u), LevelMatch X Tr hK := by
  obtain ⟨wt, hw⟩ := GlobalTheory.St.WittT.wittExists D X u
  obtain ⟨ιA, hι⟩ := hι
  obtain ⟨g0, hg0⟩ := GlobalTheory.St.G.genusMatch_holds D F X u wt ιA hw hι
  obtain ⟨h0, hL, hKm⟩ := GlobalTheory.St.G.levelConj_holds D F X hK u wt ιA g0 hw hι hg0
  choose hcf hcr using GlobalTheory.St.G.hcExists_all D F X u wt ιA h0 hw hι
  obtain ⟨J, hJ1, hJ2, hJ3⟩ := GlobalTheory.jExists_all D F X u wt hw
  exact ⟨⟨wt, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2, ιA, hι.1, hι.2, h0, hcf, hcr, J, hJ1, hJ2, hJ3⟩, hL, hKm⟩


open Formalism.L2.SG.SplitPrimeNormLemmas in
theorem exists_setting (hSW : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent)
    (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) :
      ∃ (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), X.B.I = Formalism.L2.SG.InstExistsPf.instOf D ∧
        (∀ x : X.B.I.E, HEq (X.ιE x) x) ∧ X.MeasTie hb ∧ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ ∧
        Formalism.L2.SG.LocVol.IsStdChar ψ ∧
        Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ ∧ (∀ w, Formalism.L2.SG.LocVol.LocCompatX X ψ w) ∧
        ∀ hK : X.LevelSubgroupCharacter, ∀ u, ∃ Tr : Transport X u (F u), LevelMatch X Tr hK := by
  have hB : BesselNVGap := Formalism.L2.SG.Closed.BesselNVGap_holds
  have hC : CoefWeightedLoc := Formalism.L2.SG.Closed.CoefWeightedLoc_holds
  let A := Formalism.L2.SG.InstExistsPf.instanceOfRecord D
  obtain ⟨L⟩ := GlobalTheory.St.Lat.latExists_of_forms0 D (F D.u₀)
  obtain ⟨P⟩ := Formalism.L2.SG.Closed.PsiExists_holds D A
  obtain ⟨Rf⟩ := Formalism.L2.SG.Closed.RefExists_holds D A L
  obtain ⟨Xu⟩ := Formalism.L2.SG.Closed.XuExists_holds D A L Rf
  obtain ⟨Bu⟩ := Formalism.L2.SG.Closed.BunExists_holds D hC hG A L P Rf
  obtain ⟨Pi⟩ := Formalism.L2.SG.Closed.PiExists_holds D A L
  obtain ⟨Mu⟩ := Formalism.L2.SG.Closed.MuExists_holds D A L
  obtain ⟨Wb⟩ := GlobalTheory.WBlockExists.realPlaceFunctionBlockExists_of_bessel_coef hB hC D hG A L P Rf Bu Pi Mu
  obtain ⟨Mb, hb, hM⟩ := GlobalTheory.St.mExists_holds D A L P Rf Xu Bu Pi Mu Wb
  obtain ⟨mg, hg, mw, hw, hM', ψ, hψ, hstd, hCm, hL⟩ :=
    GlobalTheory.St.Rescale.rescaleStep3 hSW D (mk A L P Rf Xu Bu Pi Mu Wb Mb) hb hM
  refine ⟨Formalism.L2.SG.SettingExistsMeasured.withMeas (mk A L P Rf Xu Bu Pi Mu Wb Mb) mg hg mw hw, hb, ψ, rfl,
    fun _ => HEq.rfl, hM', hψ, hstd, hCm, hL, fun hK u => ?_⟩
  exact exists_transport F _ hK ⟨RingEquiv.refl _, fun _ => rfl, fun _ => Iff.rfl⟩ u

end GlobalTheory.St.SpectralData
end
end
