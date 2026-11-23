module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle013
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle425
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle424
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle045
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieNilpotentCoordinates
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle422
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.HaarEqSmul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle423
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle257
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle058
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieNilpotentEqLebesgue
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle246
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealOrbitalIntegralHsNormEqProdLocal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle016
public import Formalism.UnipotentAdelicQuotients.Bundle003
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle426
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle230
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle231
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle419
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle374
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle002
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq

@[expose] public section

section

open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

theorem _root_.GlobalTheory.T.equalWordGenericBound_of_normalisedSteps : PN.NGChain → StepClassG → StepNormalsG → StepPointsG → StepNormOneG → TieOfCtx → StepChoiceConstantsC → StepPinExists → StepTermVanishG → StepLocGenPinnedG → StepThmBGP → GlobalTheory.SnPos.RowMainEqP := by
  first | exact @GlobalTheory.SnPos.rowMainEqP_of_pinned | exact GlobalTheory.SnPos.rowMainEqP_of_pinned | (intros; apply GlobalTheory.SnPos.rowMainEqP_of_pinned <;> assumption)
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.TypeAsm.TailTopGap

theorem tailP_of_gap : GlobalTheory.GapIn.Hyp → TailP := by
  intro hH Cg cb Cw cT CT C0 _ _
  obtain ⟨CH, hCH, hmom⟩ := GlobalTheory.T.majorantLength_twoSidedMoments_largeGap hH Cg cb Cw cT CT C0
  refine ⟨CH, hCH, fun C₁ => ⟨0, max 1000 (C₁ : ℝ), fun C' Cl _ hCl D large₂ _ hK hTr => ?_⟩⟩
  have hZ : HypZ D large₂ C' Cl Cg cb Cw cT CT C0 := hK.1
  have h1000 : (1000 : ℝ) ≤ Cl := le_trans (le_max_left _ _) hCl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv, -, -, -, -, hClm, -⟩ := hK.1.1

  have hC₁m : C₁ ≤ D.R.m := by
    have h : (C₁ : ℝ) ≤ (D.R.m : ℝ) := le_trans (le_max_right _ _) (le_trans hCl hClm)
    exact_mod_cast h
  have hrS : D.R.rS ≤ D.R.m := by
    unfold Formalism.BasicNotions.Ranks.rS
    omega
  have hm1 : 1 ≤ D.R.m := le_trans (by norm_num) D.R.two_le_m
  have hq : C₁ * D.R.k * D.R.rS ≤ D.R.k * D.R.m ^ 3 := by
    have h2 : C₁ * D.R.rS ≤ D.R.m ^ 3 :=
      calc C₁ * D.R.rS ≤ D.R.m * D.R.m := Nat.mul_le_mul hC₁m hrS
        _ ≤ D.R.m * D.R.m * D.R.m := Nat.le_mul_of_pos_right _ (by omega)
        _ = D.R.m ^ 3 := by ring
    calc C₁ * D.R.k * D.R.rS = D.R.k * (C₁ * D.R.rS) := by ring
      _ ≤ D.R.k * D.R.m ^ 3 := Nat.mul_le_mul_left _ h2
  have hb : 0 < large₂.sc.b := Real.exp_pos _
  have hH1 : 0 < large₂.sc.b ^ (CH * (D.R.m : ℝ)) := Real.rpow_pos_of_pos hb _

  have hTrpos : ∀ w, 0 < Tr D w := by
    intro w
    have hk : 0 ≤ Formalism.MainNotions.S.Bridge.kaS D ^ (2 * D.R.rS) := (even_two_mul _).pow_nonneg _
    by_contra hneg
    push_neg at hneg
    have h0 : Tr D w * Formalism.MainNotions.S.Bridge.kaS D ^ (2 * D.R.rS) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hneg hk
    linarith [hTr w]
  have hv0 : 0 < D.host.v := by linarith
  intro τ u W hW A hA

  have side : ∀ W' : LocW D.R.k D.R.rS, GoodW D τ u u 1 W' → ∀ A' : LocS W', GoodS D (lamD D τ) A' →
      TailBd W'.z W'.νS A'.Φ (C₁ * D.R.k * D.R.rS) (large₂.sc.b ^ (CH * (D.R.m : ℝ))) := by
    intro W' hW' A' hA'
    obtain ⟨hM, hI⟩ := hmom D large₂ C' Cl h1000 hZ τ u W' hW' A' hA' _ hq
    obtain ⟨hzW, -, -, -, -, hG, hWH, -, hN, hQ, -, -, hcont, -, -⟩ :=
      (GlobalTheory.T.amplitude_one_side_of_good_local_data D τ u u 1 W' (lamD D τ) A' hv0 one_pos (hTrpos u) (hTrpos u) hW' hA').1
    have hnull : W'.νS {x | Matrix.of x ∉ GG D.R.k D.R.rS} = 0 := by
      have hf := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hWH hN
      exact ae_iff.mp (Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 hf.1 hf.2 hQ)
    exact GlobalTheory.T.majorantLengthTailBound_of_moments D.R.k D.R.rS W'.z W'.νS A'.Φ _ _ hzW hH1 hnull hcont hM hI

  exact ⟨side W hW A hA, GlobalTheory.T.majorantLengthTailBound_primed_of_unprimed D τ u 1 (lamD D τ) _ _ side W hW A hA⟩

end GlobalTheory.TypeAsm.TailTopGap
end

section

open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CellPieriG

open GlobalTheory.CellPieri

variable {k r : ℕ}

theorem amp_eq_orb (hH : GlobalTheory.GapIn.Hyp) (hA : GlobalTheory.GapIn.AmpKF0) (hC : CellConv) (L : LocBessel k r) (R : Rep k r)
    (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (μG : Measure (Mt k r)) (l : R.H → L.Wp) (l' : R.H → L.Wq) (w : R.H)
    [CompleteSpace L.Wp] [CompleteSpace L.Wq]
    (hR : R.IsDS L.ε mu) (hgap : GapAtLeast L.ε mu h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) (hcell : GapCell k r h)
    (hc : L.c ≠ 0) (hκ : L.κN ≠ ⊤) (hG : IsHaarOn (UH (Hpk k r)) μG)
    (hl : ∀ x ∈ R.sm, ∀ v ∈ R.TK,
      Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π R.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x))
    (hl' : ∀ x ∈ R.sm, ∀ v ∈ R.TK,
      Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' R.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x))
    (hw : PI.UpqRep.IsLowUnitH k r L.ε mu R.σ w)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r))
    (ν : Measure (PairSp k r)) (hD : CellData L μG γ μR νR ν) (v v' : R.H) (hv : R.KFin v) (hv' : R.KFin v')
    (ξ : L.Wp) (ξ' : L.Wq) :
    Integrable (besselIntg L (coefR R v v' ξ ξ') γ) ν ∧
      ((PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ) * (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ)) • amp R l l' w νR γ =
        OrbInt L (coefR R v v' ξ ξ') γ ν := by
  have hKF : PI.KFinSmooth := hH.1.1.2.2.1
  obtain ⟨-, -, -, -, hsm, -, hKT, -, -⟩ := GlobalTheory.rep_basic_of_isDS hKF k r L.ε mu R hR
  have hwK : R.KFin w := PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hw
  have hle : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w, x ∈ R.TK := by
    intro x hx
    refine Submodule.span_mono ?_ hx
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g, hg, w, hwK, rfl⟩
  have hD' : CellData (withRep L R mu hR) μG γ μR νR ν := hD
  obtain ⟨b, hb0, hb1, hb2⟩ := hC k r L h μG γ μR νR ν hκ hok hcell hD hD.2.2.1
  have hAG : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity
  have hOne : OnePlaceKF (withRep L R mu hR) h μG w l l' :=
    ⟨⟨hgap, hok, hc, hw, hG, fun x hx y hy => hl x (hsm x (hle x hx)) y (hle y hy),
      fun x hx y hy => hl' x (hsm x (hle x hx)) y (hle y hy)⟩,
      fun x hx y hy => hl x (hsm x (hle x hx)) y (hKT y hy),
      fun x hx y hy => hl' x (hsm x (hle x hx)) y (hKT y hy)⟩
  have h1 := hA k r (withRep L R mu hR) h μG w l l' hOne γ μR νR ν hD' b hb0 hb1 hb2 v v' hv hv' ξ ξ'
  have h2 := (GlobalTheory.T.integrable_cellOrbitalIntegral_rankOne_kFinite hH k r (withRep L R mu hR) h μG γ μR νR ν hgap hok hκ hD').2 b hb0 (by linarith)
    hb2 v v' hv hv' ξ ξ'
  refine ⟨h2, ?_⟩
  obtain ⟨c, hc0, hc1⟩ := Gp91.GlobalTheory.BesselDegree.schur_fdeg hH.1 k r L.ε μG hG
  have hw0 : w ≠ 0 := by
    obtain ⟨P, -, hn, -⟩ := hw
    intro h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  have hDG : R.IsDG L.ε mu := ⟨hR.1, hR.2, h, hgap, hok⟩
  have hf : (PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ) ≠ 0 := by
    rw [(hc1 mu R hDG).1 w hw0]
    exact Complex.ofReal_ne_zero.mpr (mul_pos hc0 (fdegHC_pos hR.1.1)).ne'
  have h3 : (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • amp R l l' w νR γ =
      ((PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ)⁻¹) • OrbInt L (coefR R v v' ξ ξ') γ ν := h1
  rw [mul_smul, h3, smul_smul, mul_inv_cancel₀ hf, one_smul]

theorem amp_pieri : GlobalTheory.GapIn.Hyp → GlobalTheory.GapIn.AmpKF0 → CellConv → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (L : LocBessel k r) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (h : ℝ) (μG : Measure (Mt k r)) (om om' : ι → ℂ) (l : R.H → L.Wp) (l' : R.H → L.Wq) (lI : ∀ I, (RI I).H → L.Wp) (lI' : ∀ I, (RI I).H → L.Wq) (w : R.H) (wI : ∀ I, (RI I).H) (κ₀ κ₁ : κ → ℂ), haveI := FiniteDimensional.complete ℂ L.Wp; haveI := FiniteDimensional.complete ℂ L.Wq; R.IsDS L.ε mu → GapAtLeast L.ε mu h → (∀ I, (RI I).IsDS L.ε (muI I) ∧ GapAtLeast L.ε (muI I) h) → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GapCell k r h → L.c ≠ 0 → L.κN ≠ ⊤ → IsHaarOn (UH (Hpk k r)) μG → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → (∀ g ∈ Sset k r L.z, ρ g *ᵥ om = om) → (∀ g ∈ Sset k r L.z', ρ g *ᵥ om' = om') → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π R.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' R.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∀ I, (∀ x ∈ (RI I).sm, ∀ v ∈ (RI I).TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π (RI I).σ L.μW L.μN x v = (innerSL ℂ (lI I v)).smulRight (lI I x)) ∧ (∀ x ∈ (RI I).sm, ∀ v ∈ (RI I).TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' (RI I).σ L.μW' L.μN x v = (innerSL ℂ (lI' I v)).smulRight (lI' I x))) → (∃ v, R.KFin v ∧ l v ≠ 0) → (∃ v, R.KFin v ∧ l' v ≠ 0) → PI.UpqRep.IsLowUnitH k r L.ε mu R.σ w → (∀ I, PI.UpqRep.IsLowUnitH k r L.ε (muI I) (RI I).σ (wI I)) → (∀ I, ∀ v ∈ R.sm, lI I (∑ c, pr I c (tm R om v c)) = κ₀ I • l v ∧ lI' I (∑ c, pr I c (tm R om' v c)) = κ₁ I • l' v) → ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r)) (ν : Measure (PairSp k r)), CellData L μG γ μR νR ν → (herm Γ (ρ γ *ᵥ om') om * (PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ)) • amp R l l' w νR γ = ∑ I, ((ep I : ℂ) * κ₁ I * star (κ₀ I) * (PI.BesselPeriodGGP.fdegH μG (RI I).σ (wI I) : ℂ)) • amp (RI I) (lI I) (lI' I) (wI I) νR γ := by
  intro hH hA hC k r ι κ _ _ _ _ ρ Γ d L R RI io pr ep mu muI h μG om om' l l' lI lI' w wI κ₀ κ₁
  haveI := FiniteDimensional.complete ℂ L.Wp
  haveI := FiniteDimensional.complete ℂ L.Wq
  intro hR hgap hRI hok hcell hc hκ hG hρ hT hom hom' hl hl' hlI ⟨v, hv, hv0⟩ ⟨v', hv', hv0'⟩ hw hwI hκI γ μR νR ν hD
  have hKF : PI.KFinSmooth := hH.1.1.2.2.1
  have hvs : v ∈ R.sm := hKF k r L.ε mu R.H R.σ hR.1 hR.2 v hv
  have hvs' : v' ∈ R.sm := hKF k r L.ε mu R.H R.σ hR.1 hR.2 v' hv'
  obtain ⟨hK, hsplit⟩ := GlobalTheory.KFinCoefSplit.kfin_coef_mul_split hKF k r ι κ ρ Γ d R RI io pr ep L.ε mu muI om om' v v' hR
    (fun I => (hRI I).1) hρ hT hv hv'
  obtain ⟨-, e0⟩ := amp_eq_orb hH hA hC L R mu h μG l l' w hR hgap hok hcell hc hκ hG hl hl' hw γ μR νR ν hD
    v v' hv hv' (l v) (l' v')
  have eI := fun I => amp_eq_orb hH hA hC L (RI I) (muI I) h μG (lI I) (lI' I) (wI I) (hRI I).1 (hRI I).2 hok hcell
    hc hκ hG (hlI I).1 (hlI I).2 (hwI I) γ μR νR ν hD _ _ (hK I).1 (hK I).2 (l v) (l' v')
  have hae := (GlobalTheory.T.integrable_cellOrbitalIntegral_rankOne_kFinite hH k r (withRep L R mu hR) h μG γ μR νR ν hgap hok hκ hD).1
  have hc0 : ⟪l v, l v⟫_ℂ * ⟪l' v', l' v'⟫_ℂ ≠ 0 :=
    mul_ne_zero (inner_self_ne_zero.mpr hv0) (inner_self_ne_zero.mpr hv0')
  have horb : herm Γ (ρ γ *ᵥ om') om • OrbInt L (coefR R v v' (l v) (l' v')) γ ν =
      ∑ I, (ep I : ℂ) • OrbInt L (coefR (RI I) (∑ c, pr I c (tm R om v c)) (∑ c, pr I c (tm R om' v' c))
        (l v) (l' v')) γ ν := by
    unfold OrbInt
    simp only [← integral_smul]
    refine Eq.trans (integral_congr_ae ?_) (integral_finsetSum _ (fun I _ => (eI I).1.smul (ep I : ℂ)))
    filter_upwards [hae] with p hp
    obtain ⟨hm, he⟩ := herm_cell hρ hom hom' hD.1 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
    have hs := hsplit _ hm
    rw [he] at hs
    ext x
    simp only [besselIntg, coefR, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply, map_smul, smul_smul, Pi.smul_apply,
      ← Finset.sum_smul]
    congr 1
    have key : ∀ (D A B C : ℂ) (e f : κ → ℂ), D * C = ∑ I, e I * f I →
        D * A * (B * C) = ∑ I, e I * A * (B * f I) := by
      intro D A B C e f hh
      rw [show D * A * (B * C) = D * C * (A * B) by ring, hh, Finset.sum_mul]
      exact Finset.sum_congr rfl fun I _ => by ring
    exact key _ _ _ _ _ _ hs
  apply smul_right_injective _ hc0
  simp only [Finset.smul_sum, smul_smul]
  rw [mul_comm, mul_assoc, mul_smul, e0, horb]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← (eI I).2, smul_smul, (hκI I v hvs).1, (hκI I v' hvs').2, inner_smul_left, inner_smul_right]
  congr 1
  simp only [RCLike.star_def]
  ring

end GlobalTheory.CellPieriG

end
end

section

open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.amplitude_eq_kFiniteOrbitalIntegral_gap : GlobalTheory.GapIn.Hyp → GlobalTheory.GapIn.AmpKF0 := by
  first | exact @GlobalTheory.AmpOrbGap.ampKF | exact GlobalTheory.AmpOrbGap.ampKF | (intros; apply GlobalTheory.AmpOrbGap.ampKF <;> assumption)
end

section

open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.QuantumDeterminants GlobalTheory.ThA

theorem _root_.GlobalTheory.T.besselPointwiseBound_at_largeGaps : GlobalTheory.GapIn.Hyp → ThmBpDS → ∀ Ch : ℝ, ∃ Cb Cg₀ : ℝ, ∀ Cg : ℝ, Cg₀ ≤ Cg → (∀ (D : D7) (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (f : B.Mat D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b : ℝ), LocOk D Ch Cg L lam0 ka b 1 → AllGaps lam0 (200 * l1 L.lam lam0) → IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec → ∀ γ : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → BpIneq D Cb L f μsec b γ) ∧ (∀ D : D7, Formalism.MainNotions.OnePlaceEstimates.TheoremBPrimePointwise D Ch Cg Cb) ∧ ∀ (D : D7) (Cu Cg' : ℝ), 200 * Cu ≤ Cg' → Formalism.MainNotions.OnePlaceEstimates.UniformityTheoremBPrime D Ch Cu Cg Cg' Cb := by
  first | exact @GlobalTheory.bp_forms_of_gapIn_thmBpDS | exact GlobalTheory.bp_forms_of_gapIn_thmBpDS | (intros; apply GlobalTheory.bp_forms_of_gapIn_thmBpDS <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN.BlockMeas

abbrev Yf (k r : ℕ) : Type := (NEntry.Idx k r → ℂ) × (UTr r → ℂ) × (Fin r → ℝ)

abbrev Ys (k r : ℕ) : Type :=
  ((UTr r → ℂ) × (Fin r → Fin (k + 1) → ℂ)) × ((UTr r → ℂ) × (Fin r → ℝ))

abbrev Zb (ι : Type) (k r : ℕ) : Type :=
  (UTr r → ι → ℂ) × (Fin r → ι → Fin (k + 1) → ℂ) × (UTr r → ι → ℂ) × (Fin r → ι → ℝ)

def sp (ι : Type) (k r : ℕ) (y : ι → Yf k r) : Zb ι k r :=
  (fun p w => (y w).1 (NEntry.idx k r (.inl p)), fun a w j => (y w).1 (NEntry.idx k r (.inr (a, j))),
    fun p w => (y w).2.1 p, fun a w => (y w).2.2 a)

def sq (ι : Type) (k r : ℕ) (y : ι → Ys k r) : Zb ι k r :=
  (fun p w => (y w).1.1 p, fun a w => (y w).1.2 a, fun p w => (y w).2.1 p, fun a w => (y w).2.2 a)

theorem sq_mp (ι : Type) [Fintype ι] (k r : ℕ) : MeasurePreserving (sq ι k r) volume volume := by
  have h1 := volume_measurePreserving_arrowProdEquivProdArrow ((UTr r → ℂ) × (Fin r → Fin (k + 1) → ℂ))
    ((UTr r → ℂ) × (Fin r → ℝ)) ι
  have h2 := volume_measurePreserving_arrowProdEquivProdArrow (UTr r → ℂ) (Fin r → Fin (k + 1) → ℂ) ι
  have h3 := volume_measurePreserving_arrowProdEquivProdArrow (UTr r → ℂ) (Fin r → ℝ) ι
  have s1 : MeasurePreserving (fun (f : ι → UTr r → ℂ) (p : UTr r) (i : ι) => f i p) volume volume :=
    ReciprocityTheory.GeometryOfNumbersTheory.measurePreserving_swapPi (volume : Measure ℂ)
  have s2 : MeasurePreserving (fun (f : ι → Fin r → Fin (k + 1) → ℂ) (p : Fin r) (i : ι) => f i p) volume volume :=
    ReciprocityTheory.GeometryOfNumbersTheory.measurePreserving_swapPi (volume : Measure (Fin (k + 1) → ℂ))
  have s3 : MeasurePreserving (fun (f : ι → Fin r → ℝ) (p : Fin r) (i : ι) => f i p) volume volume :=
    ReciprocityTheory.GeometryOfNumbersTheory.measurePreserving_swapPi (volume : Measure ℝ)
  haveI u0 : SigmaFinite (volume : Measure (Fin (k + 1) → ℂ)) := inferInstance
  haveI u1 : SigmaFinite (volume : Measure (Fin r → Fin (k + 1) → ℂ)) := inferInstance
  haveI u2 : SigmaFinite (volume : Measure (ι → Fin (k + 1) → ℂ)) := inferInstance
  haveI t1 : SigmaFinite (volume : Measure (ι → UTr r → ℂ)) := inferInstance
  haveI t2 : SigmaFinite (volume : Measure (ι → Fin r → Fin (k + 1) → ℂ)) := inferInstance
  haveI t3 : SigmaFinite (volume : Measure (UTr r → ι → ℂ)) := inferInstance
  haveI t4 : SigmaFinite (volume : Measure (Fin r → ι → Fin (k + 1) → ℂ)) := inferInstance
  have a := s1.prod s2
  have b := s1.prod s3
  have c := (a.prod b).comp ((h2.prod h3).comp h1)
  exact (volume_preserving_prodAssoc).comp c

theorem pi_smul (ι : Type) [Fintype ι] {X : Type} [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν] (c : NNReal) :
    Measure.pi (fun _ : ι => (c : ℝ≥0∞) • ν) = ((c : ℝ≥0∞) ^ Fintype.card ι) • Measure.pi (fun _ : ι => ν) := by
  haveI : SigmaFinite ((c : ℝ≥0∞) • ν) := by
    have e : (c : ℝ≥0∞) • ν = c • ν := by
      ext s _
      simp [Measure.smul_apply]
    rw [e]
    infer_instance
  refine Measure.pi_eq fun s hs => ?_
  simp [Measure.smul_apply, Measure.pi_pi, Finset.prod_mul_distrib, smul_eq_mul]

theorem mem_iff (ι : Type) (k r : ℕ) (DU : UTr r → Set (ι → ℂ)) (DH : Fin r → Set (ι → Fin (k + 1) → ℂ))
    (DC : UTr r → Set (ι → ℂ)) (DG : Fin r → Set (ι → ℝ)) (x : ι → Mt k r) :
    (∀ β : Bk r, (fun w => cM k r β (x w)) ∈ blkSet ι k r DU DH DC DG β) ↔
      sp ι k r (fun w => nCoords k r (x w)) ∈
        Set.univ.pi DU ×ˢ Set.univ.pi DH ×ˢ Set.univ.pi DC ×ˢ Set.univ.pi DG := by
  simp only [Sum.forall, Set.mem_prod, Set.mem_univ_pi]
  exact Iff.rfl

theorem measure_blocks : ∀ (ι : Type) [Fintype ι] (k r : ℕ) (DU : UTr r → Set (ι → ℂ)) (DH : Fin r → Set (ι → Fin (k + 1) → ℂ)) (DC : UTr r → Set (ι → ℂ)) (DG : Fin r → Set (ι → ℝ)), (∀ p, MeasurableSet (DU p)) → (∀ a, MeasurableSet (DH a)) → (∀ p, MeasurableSet (DC p)) → (∀ a, MeasurableSet (DG a)) → MeasurableSet {x : ι → Mt k r | (∀ w, Matrix.of (x w) ∈ Nset k r) ∧ ∀ β : Bk r, (fun w => cM k r β (x w)) ∈ blkSet ι k r DU DH DC DG β} ∧ (Measure.pi fun _ : ι => haarLie (Nset k r) 1) {x : ι → Mt k r | (∀ w, Matrix.of (x w) ∈ Nset k r) ∧ ∀ β : Bk r, (fun w => cM k r β (x w)) ∈ blkSet ι k r DU DH DC DG β} = (2 : ℝ≥0∞) ^ (Fintype.card ι * (r * (r - 1) + r * (k + 1))) * ((∏ p, volume (DU p)) * (∏ a, volume (DH a)) * (∏ p, volume (DC p)) * ∏ a, volume (DG a)) := by
  intro ι _ k r DU DH DC DG hU hH hC hG
  obtain ⟨⟨hσ, -, hnull, -⟩, -, -, hmap⟩ := GlobalTheory.T.haar_lie_nilpotent_coordinates k r
  set μ := haarLie (Nset k r) 1 with hμ
  set e := r * (r - 1) + r * (k + 1) with he
  set F : (ι → Mt k r) → (ι → Yf k r) := fun x w => nCoords k r (x w) with hFdef
  set R : Set (Zb ι k r) := Set.univ.pi DU ×ˢ Set.univ.pi DH ×ˢ Set.univ.pi DC ×ˢ Set.univ.pi DG with hRdef
  have hF : Measurable F :=
    Measurable.of_eval fun w => NEntry.cont_nCoords.measurable.comp (measurable_pi_apply w)
  have hsp : Measurable (sp ι k r) := by
    unfold sp
    fun_prop
  have hR : MeasurableSet R :=
    (MeasurableSet.univ_pi hU).prod ((MeasurableSet.univ_pi hH).prod
      ((MeasurableSet.univ_pi hC).prod (MeasurableSet.univ_pi hG)))
  have hNm : MeasurableSet {x : Mt k r | Matrix.of x ∈ Nset k r} := by
    have : IsClosed {x : Mt k r | Matrix.of x ∈ Nset k r} := GlobalTheory.Amp.NLie.closed_N
    exact this.measurableSet
  have hNi : MeasurableSet {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r} := by
    have : {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r} =
        Set.univ.pi fun _ => {x : Mt k r | Matrix.of x ∈ Nset k r} := by
      ext x
      simp
    rw [this]
    exact MeasurableSet.univ_pi fun _ => hNm
  have hS : {x : ι → Mt k r | (∀ w, Matrix.of (x w) ∈ Nset k r) ∧
      ∀ β : Bk r, (fun w => cM k r β (x w)) ∈ blkSet ι k r DU DH DC DG β} =
      (sp ι k r ∘ F) ⁻¹' R ∩ {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Function.comp_apply]
    rw [mem_iff]
    exact and_comm
  rw [hS]
  refine ⟨((hsp.comp hF) hR).inter hNi, ?_⟩
  have hconull : (Measure.pi fun _ : ι => μ) {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r}ᶜ = 0 := by
    have : {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r}ᶜ ⊆
        ⋃ w, Function.eval w ⁻¹' {x : Mt k r | Matrix.of x ∉ Nset k r} := by
      intro x hx
      simpa using hx
    refine measure_mono_null this (measure_iUnion_null fun w => ?_)
    exact Measure.pi_eval_preimage_null _ hnull
  rw [measure_inter_conull hconull]
  have hc : ((2 : ℝ≥0∞) ^ e) = ((2 ^ e : NNReal) : ℝ≥0∞) := by
    push_cast
    rfl
  haveI : SigmaFinite (μ.map (nCoords k r)) := by
    rw [hmap, hc]
    have e' : ((2 ^ e : NNReal) : ℝ≥0∞) • (volume : Measure (Yf k r)) = (2 ^ e : NNReal) • volume := by
      ext s _
      simp [Measure.smul_apply]
    rw [e']
    infer_instance
  have hpi : (Measure.pi fun _ : ι => μ).map F = Measure.pi fun _ : ι => μ.map (nCoords k r) :=
    Measure.pi_map_pi (fun _ => NEntry.cont_nCoords.measurable.aemeasurable)
  have hpre : (sp ι k r ∘ F) ⁻¹' R = F ⁻¹' (sp ι k r ⁻¹' R) := rfl
  rw [hpre, ← Measure.map_apply hF (hsp hR), hpi, hmap, hc, pi_smul, Measure.smul_apply, smul_eq_mul]

  have hΦ : MeasurePreserving (fun (y : ι → Ys k r) w => ((NEntry.glue (y w).1, (y w).2) : Yf k r)) volume volume :=
    volume_preserving_pi (f := fun _ : ι => Prod.map (NEntry.glue (k := k) (r := r)) id)
      fun _ => (NEntry.glue_mp (k := k) (r := r)).1.prod (MeasurePreserving.id _)
  have hcomp : (fun (y : ι → Ys k r) w => ((NEntry.glue (y w).1, (y w).2) : Yf k r)) ⁻¹' (sp ι k r ⁻¹' R) =
      sq ι k r ⁻¹' R := by
    ext y
    have : sp ι k r (fun w => ((NEntry.glue (y w).1, (y w).2) : Yf k r)) = sq ι k r y := by
      simp [sp, sq, NEntry.glue]
    simp only [Set.mem_preimage, this]
  have hvol : (Measure.pi fun _ : ι => (volume : Measure (Yf k r))) (sp ι k r ⁻¹' R) = volume R := by
    have h1 := hΦ.measure_preimage (hsp hR).nullMeasurableSet
    rw [hcomp, (sq_mp ι k r).measure_preimage hR.nullMeasurableSet] at h1
    exact h1.symm
  haveI u0 : SigmaFinite (volume : Measure (Fin (k + 1) → ℂ)) := inferInstance
  haveI u2 : SigmaFinite (volume : Measure (ι → Fin (k + 1) → ℂ)) := inferInstance
  haveI t3 : SigmaFinite (volume : Measure (UTr r → ι → ℂ)) := inferInstance
  haveI t4 : SigmaFinite (volume : Measure (Fin r → ι → Fin (k + 1) → ℂ)) := inferInstance
  haveI t5 : SigmaFinite (volume : Measure (Fin r → ι → ℝ)) := inferInstance
  have hpow : ((2 ^ e : NNReal) : ℝ≥0∞) ^ Fintype.card ι = (2 : ℝ≥0∞) ^ (Fintype.card ι * e) := by
    rw [← hc, ← pow_mul, mul_comm]
  rw [hvol, hRdef, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod,
    Measure.volume_eq_prod, Measure.prod_prod, volume_pi_pi, volume_pi_pi, volume_pi_pi, volume_pi_pi, hpow]
  simp only [mul_assoc]

end GlobalTheory.SnMass.VolN.BlockMeas
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem actM_measurePreserving (E : Type) [Field E] [NumberField E] (k r : ℕ)
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (hN : ∀ w, gM A γ w ∈ Nset k r) :
    MeasurePreserving (actM A γ) (Measure.pi fun _ : InfinitePlace E => haarLie (Nset k r) 1)
      (Measure.pi fun _ : InfinitePlace E => haarLie (Nset k r) 1) := by
  have hH := (GlobalTheory.T.haar_lie_nilpotent_coordinates k r).1
  haveI : SigmaFinite (haarLie (Nset k r) 1) := hH.1
  have hf : ∀ w, MeasurePreserving (lmulM (gM A γ w)) (haarLie (Nset k r) 1) (haarLie (Nset k r) 1) :=
    fun w => ⟨GlobalTheory.Amp.StabMeas.meas_lmul _, hH.2.2.2 _ (hN w)⟩
  exact measurePreserving_pi (fun _ : InfinitePlace E => haarLie (Nset k r) 1) (fun _ => haarLie (Nset k r) 1) hf

end GlobalTheory.SnMass.VolN
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.realOrbitalIntegral_hsNorm_eq_prod_local : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (μl νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) (ν : Measure X.B.I.Ginf), (∀ v, Formalism.L2.SG.RealObj.IsHaarLoc (Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (γ v)) (μl v)) → (∀ v, Formalism.L2.SG.RealObj.IsQuotLoc (μl v) (νl v)) → IsQuotMeasS X.B.I (Measure.pi μl) ν → (∀ v, ∀ s ∈ Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (γ v), ∀ x, Formalism.L2.SG.TermOp.rk1 (X.Wloc u v (s * x)) (X.Wloc u' v ((γ v)⁻¹ * (s * x))) = Formalism.L2.SG.TermOp.rk1 (X.Wloc u v x) (X.Wloc u' v ((γ v)⁻¹ * x))) → hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vpi u); Formalism.L2.SG.TermOp.OO ν Set.univ (X.Wu u) (X.Wu u') γ) = ∏ v, hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v); Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u' v) (γ v)) := by
  first | exact @GlobalTheory.OrbQuotProd.oo_quot | exact GlobalTheory.OrbQuotProd.oo_quot | (intros; apply GlobalTheory.OrbQuotProd.oo_quot <;> assumption)
end

section


theorem _root_.GlobalTheory.T.familyStep_of_four_globalLeaves : Formalism.L2.SG.FamDefs.OrbitFamilyIdentityNonGeneric → Formalism.L2.SG.FamDefs.WeightsNG → Formalism.L2.SG.FamDefs.ProductStructureNonGeneric → Formalism.L2.SG.FamDefs.ExistNG → Formalism.L2.SG.NGLocModel.StepFamC := by
  first | exact @GlobalTheory.stepFamC_of_globalLeaves | exact GlobalTheory.stepFamC_of_globalLeaves | (intros; apply GlobalTheory.stepFamC_of_globalLeaves <;> assumption)
end

section

open Formalism.MainNotions Formalism.MainNotions.S MeasureTheory

namespace GlobalTheory.CountConstants

theorem count_constants_of_siegelWeil :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∃ (c30 : List ℝ → Formalism.MainNotions.S.CountingConstants) (cIc : ℝ),
      (∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A) ∧ 0 < cIc ∧
      (∀ {eps : ℝ} (Fm : FamP eps), cIc ≤ (c30 Fm.cOut).c) ∧
      ∀ (P : ∀ I : AutInst, Measure I.Gf → ℕ → (I.Gf → ℂ) → Prop) {eps : ℝ} (Fm : FamP eps),
        CountE.CountAllPointsClass P Fm (c30 Fm.cOut).n0 (c30 Fm.cOut).A (c30 Fm.cOut).C (c30 Fm.cOut).c (c30 Fm.cOut).cb := by
  intro hSW
  have H := GlobalTheory.CountBridge.count_typed_of_volumeStep (GlobalTheory.GaussMean.volumeStep_of_siegelWeil hSW)
  choose n₀ C₀ hC₀ HC using H
  let Af : List ℝ → ℝ := fun l => 2 * (l.getD 6 0 + 1)
  refine ⟨fun l => ⟨0, n₀ (Af l), Af l, 0, C₀ (Af l), 1 / 16, 1 / 16⟩, 1 / 16,
    fun Fm => ⟨hC₀ _, le_refl _⟩, by norm_num, fun Fm => le_refl _, fun P {_} Fm => ⟨by norm_num, by norm_num, ?_⟩⟩
  intro x i
  exact CountE.count_class_of_count P (HC _ _ le_rfl _ le_rfl _)

end GlobalTheory.CountConstants
end
