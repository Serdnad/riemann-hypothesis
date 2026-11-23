module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle040
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemma3
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TopsChoicePartA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BaseOf
public import Formalism.HermitianCurvature.Bundle006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle035
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle039
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle034

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open scoped ENNReal
open Matrix

set_option linter.unusedVariables false

namespace Formalism.L2.SG.Pf.GoodS

theorem nu_conc {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z)
    {μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)} (hG : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG)
    (hS : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Sset k r z) μS) (hq : Formalism.MainNotions.S.IsQuotMeas μG μS ν) :
    ν {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0 := by
  classical
  have hUH : ∀ a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) →
      a * b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    intro a b ha hb
    have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
    have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
    show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.QuantumDeterminants.Hpk k r := by rw [ha', hb']
  have hSG : ∀ M, M ∈ Formalism.QuantumDeterminants.Sset k r z → M ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    rintro M ⟨g, hg, m, hm, rfl⟩
    exact hUH g m hg.1 hm.1
  have hc : Continuous fun x : Formalism.QuantumDeterminants.Mt k r =>
      (Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of x := by
    have h0 : Continuous fun x : Formalism.QuantumDeterminants.Mt k r => Matrix.of x := continuous_id
    exact (h0.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul h0
  have hBm : MeasurableSet
      {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} := by
    have hcl : IsClosed {x : Formalism.QuantumDeterminants.Mt k r |
        (Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of x = Formalism.QuantumDeterminants.Hpk k r} :=
      isClosed_eq hc continuous_const
    exact hcl.measurableSet.compl
  have hq1 := hq
    ({x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)}.indicator
      fun _ => (1 : ℝ≥0∞)) (measurable_const.indicator hBm)
  rw [lintegral_indicator_const hBm, hG.2.2.1, mul_zero] at hq1
  have hpt : ∀ x : Formalism.QuantumDeterminants.Mt k r,
      ({x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)}.indicator
        fun _ => μS Set.univ) x ≤
      ∫⁻ s, ({x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)}.indicator
        fun _ => (1 : ℝ≥0∞)) (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS := by
    intro x
    by_cases hx : Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)
    · have hnm : x ∉ {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} :=
        fun h => h hx
      rw [Set.indicator_apply, if_neg hnm]
      exact bot_le
    · have hxm : x ∈ {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} := hx
      rw [Set.indicator_apply, if_pos hxm]
      calc μS Set.univ = ∫⁻ _, (1 : ℝ≥0∞) ∂μS := lintegral_one.symm
        _ ≤ _ := by
          apply lintegral_mono_ae
          have hae : ∀ᵐ s ∂μS, Matrix.of s ∈ Formalism.QuantumDeterminants.Sset k r z := ae_iff.mpr hS.2.2.1
          filter_upwards [hae] with s hs
          have hsG : (Matrix.of s)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of s = Formalism.QuantumDeterminants.Hpk k r :=
            hSG _ hs
          have hmem : (fun i j => (Matrix.of s * Matrix.of x) i j) ∈
              {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} := by
            show ¬ (Matrix.of (fun i j => (Matrix.of s * Matrix.of x) i j) ∈
              Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
            intro hG'
            have e : (Matrix.of s * Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk k r *
                (Matrix.of s * Matrix.of x) = Formalism.QuantumDeterminants.Hpk k r := hG'
            apply hx
            show (Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of x = Formalism.QuantumDeterminants.Hpk k r
            rw [Matrix.conjTranspose_mul] at e
            calc (Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of x
                = (Matrix.of x)ᴴ * ((Matrix.of s)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of s) *
                    Matrix.of x := by rw [hsG]
              _ = Formalism.QuantumDeterminants.Hpk k r := by simpa only [Matrix.mul_assoc] using e
          simp only [Set.indicator_of_mem hmem, le_refl]
  have hle := lintegral_mono (μ := ν) hpt
  rw [lintegral_indicator_const hBm, ← hq1] at hle
  have hpos : μS Set.univ ≠ 0 := (Measure.measure_univ_pos.mpr hS.2.1).ne'
  rcases mul_eq_zero.mp (nonpos_iff_eq_zero.mp hle) with h | h
  · exact absurd h hpos
  · exact h

def toUJn {n : ℕ} {ε : Fin n → Bool} (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε) : Formalism.REAL.UJ ε :=
  ⟨⟨M, Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε,
    (Matrix.mul_eq_one_comm_of_card_eq (Fin n) (Fin n) ℂ rfl).mp (by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM, Formalism.REAL.Jm_mul_self]),
    by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM, Formalism.REAL.Jm_mul_self]⟩, hM⟩

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem phi_eq (C : Choice X θ) (hB : WuBessel C) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (m : Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS) (hm : m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    phiOf hB u τ m = wT C u τ (m * C.y τ) := by
  obtain ⟨h1, h2, hg, -⟩ := C.isT τ
  have hy := C.y_mem τ
  obtain ⟨hrep, -⟩ := Formalism.L2.SG.Pf.WuBL.sigB_rep C τ
  have hmy : m * C.y τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := Formalism.MainNotions.S.Inh.mul_mem_UH_Hpk_nonempty_parameter_models _ _ hm hy
  have hJ : (C.Q τ * (m * C.y τ) * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * (m * C.y τ) * C.Qi τ) =
      Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
    have hmy' : (m * C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (m * C.y τ) = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hmy
    calc (C.Q τ * (m * C.y τ) * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * (m * C.y τ) * C.Qi τ)
        = (C.Qi τ)ᴴ * ((m * C.y τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * (m * C.y τ)) *
            C.Qi τ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by rw [hg, hmy', qiHqi _ h2 hg]
  set γ := toUJn (C.Q τ * (m * C.y τ) * C.Qi τ) hJ
  have hγ : uMat γ = C.Q τ * (m * C.y τ) * C.Qi τ := rfl
  have hW := (hB u τ).choose_spec.2 γ
  have e1 : sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ) = X.B.σ (vOf X τ) (uMat γ) (X.B.w (vOf X τ)) := by
    unfold v0Of
    rw [← ContinuousLinearMap.comp_apply, ← hrep.2 _ hm _ hy, hγ]
    rfl
  unfold phiOf bOf
  rw [e1, ← hW, ← Formalism.L2.SG.Pf.WuBL.wT_at C u τ γ, hγ]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem l2SG_phiOf_ne_zero_and_lt_infty (C : Choice X θ) (hLF : LocFactor C) (hB : WuBessel C) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    l2SG (C.nuS u τ) (phiOf hB u τ) ≠ 0 ∧ l2SG (C.nuS u τ) (phiOf hB u τ) < ⊤ := by
  obtain ⟨hwsm, hw1, hSH, hWc, hWe, hWr, hne, hfin⟩ := hLF u τ
  obtain ⟨hz, hTz⟩ := Formalism.L2.SG.Pf.zTr C u τ
  have hT : 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by rw [hTz]; exact Tr_pos D u
  have hHG := Formalism.L2.SG.Pf.haarTr C τ
  have hq := C.nuS_q u τ
  have hy := C.y_mem τ
  have hconc := nu_conc hz hT hHG hSH hq
  have hπ := Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved D.R.k D.R.rS _ _ _ _ hz hT (Formalism.L2.SG.Pf.colsTypeTr C u τ)
  have hinv : ∀ s ∈ Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ), ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS),
      ‖wT C u τ (s * x)‖ = ‖wT C u τ x‖ := by
    rintro _ ⟨h0, hh0, n0, hn0, rfl⟩ x hx
    rw [hWe h0 hh0 n0 hn0 x hx, norm_smul, psiS, Formalism.L2.SG.Pf.WuBL.norm_psi, one_mul, hπ.2.1 h0 hh0]
  have heq := Formalism.L2.SG.Pf.WuBL.l2RightTranslation_thm D.R.k D.R.rS _ hz hT _ _ _ hHG hSH hq _ (wT C u τ) hWc
    (Formalism.L2.SG.Pf.WuBL.wT_off C u τ) hinv (C.y τ) hy
  have hae : ∀ᵐ x ∂(C.nuS u τ), Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
    rw [ae_iff]; exact hconc
  have hphi : l2SG (C.nuS u τ) (phiOf hB u τ) = l2SG (C.nuS u τ) (fun x => wT C u τ (x * C.y τ)) := by
    unfold l2SG
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [phi_eq C hB u τ _ hx]
  rw [hphi, heq]
  exact ⟨hne, hfin⟩

end Formalism.L2.SG.Pf.GoodS
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.Pf.LoopBCovN

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def eN (D : D7) : ℝ := (D.R.rS : ℝ) ^ 2 + (D.R.rS : ℝ) / 2

def CovNFormula : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), 0 < θ →
    LoopTerm.covN (Y := Y) C u = (θ * (2 * D.host.v) ^ eN D) ^ Fintype.card D.what₂.Tau

theorem rdE_ge_one (D : D7) : 1 ≤ 2 * D.host.v := by
  unfold Formalism.BasicNotions.Host.v Formalism.BasicNotions.Host.rdE
  have hd : (1 : ℝ) ≤ |(NumberField.discr D.host.E : ℝ)| := by
    have h0 : NumberField.discr D.host.E ≠ 0 := NumberField.discr_ne_zero D.host.E
    have h1 : (1 : ℤ) ≤ |NumberField.discr D.host.E| := Int.one_le_abs h0
    exact_mod_cast h1
  have h2 : (1 : ℝ) ≤ |(NumberField.discr D.host.E : ℝ)| ^ (1 / (Module.finrank ℚ D.host.E : ℝ)) :=
    Real.one_le_rpow hd (by positivity)
  linarith

theorem covWinN_of (hF : CovNFormula) {D : D7} {X : HidaSetting D} {Y : Full X} (C : Choice X 1) (large₂ : SizeData₂ D) {C1 : ℝ}
    (hC1 : 0 ≤ C1) (hup : eN D * Real.log (2 * D.host.v) ≤ C1 * (D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b)
    (u u' : D.what₂.Word) : LoopTerm.CovWinN (Y := Y) C large₂ C1 u u' := by
  have hbpos : 0 < large₂.sc.b := by
    unfold Scale.b
    exact Real.exp_pos _
  have hv := rdE_ge_one D
  have hv0 : 0 < 2 * D.host.v := by linarith
  have heN : 0 ≤ eN D := by
    unfold eN
    positivity
  have hy1 : 1 ≤ (2 * D.host.v) ^ eN D := Real.one_le_rpow hv heN
  have hlog0 : 0 ≤ eN D * Real.log (2 * D.host.v) := mul_nonneg heN (Real.log_nonneg hv)
  have hyexp : (2 * D.host.v) ^ eN D = Real.exp (Real.log (2 * D.host.v) * eN D) :=
    Real.rpow_def_of_pos hv0 _
  have hcov : ∀ w, LoopTerm.covN (Y := Y) C w = ((2 * D.host.v) ^ eN D) ^ Fintype.card D.what₂.Tau := by
    intro w
    rw [hF D X Y 1 C w one_pos, one_mul]
  have hx : (LoopTerm.covN (Y := Y) C u * LoopTerm.covN (Y := Y) C u') ^ (1 / (2 * (Fintype.card D.what₂.Tau : ℝ))) = 1 ∨
      (LoopTerm.covN (Y := Y) C u * LoopTerm.covN (Y := Y) C u') ^ (1 / (2 * (Fintype.card D.what₂.Tau : ℝ))) =
        (2 * D.host.v) ^ eN D := by
    rw [hcov u, hcov u', ← pow_add, ← two_mul]
    rcases Nat.eq_zero_or_pos (Fintype.card D.what₂.Tau) with h0 | hpos
    · left
      simp [h0]
    · right
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      have hN : (0 : ℝ) < Fintype.card D.what₂.Tau := by exact_mod_cast hpos
      have h2 : ((2 * Fintype.card D.what₂.Tau : ℕ) : ℝ) * (1 / (2 * (Fintype.card D.what₂.Tau : ℝ))) = 1 := by
        push_cast
        field_simp
      rw [h2, Real.rpow_one]
  have hxb : ∀ z : ℝ, (z = 1 ∨ z = (2 * D.host.v) ^ eN D) → 1 ≤ z ∧ z ≤ (2 * D.host.v) ^ eN D := by
    rintro z (rfl | rfl) <;> exact ⟨by linarith, by linarith⟩
  obtain ⟨hx1, hx2⟩ := hxb _ hx
  have hup' : Real.log (2 * D.host.v) * eN D ≤ Real.log large₂.sc.b * (C1 * (D.R.m : ℝ) ^ 2) := by linarith
  unfold LoopTerm.CovWinN normWin
  refine ⟨le_trans ?_ hx1, le_trans hx2 ?_⟩
  · rw [Real.rpow_def_of_pos hbpos]
    have hneg : Real.log large₂.sc.b * -(C1 * (D.R.m : ℝ) ^ 2) ≤ 0 := by nlinarith
    exact Real.exp_le_one_iff.mpr hneg
  · rw [hyexp, Real.rpow_def_of_pos hbpos]
    exact Real.exp_le_exp.mpr hup'

theorem log_rd_le {D : D7} (large₂ : SizeData₂ D) (hS : Formalism.MainNotions.SizesAt large₂) :
    Real.log (2 * D.host.v) ≤ Real.log large₂.sc.b / 72 := by
  obtain ⟨-, -, -, -, hT, hC, hQ, -⟩ := hS
  obtain ⟨-, -, -, -, -, -, hr1, hr2⟩ := hQ
  have h2v : 2 * D.host.v = D.host.rdE := by unfold Formalism.BasicNotions.Host.v; ring
  rw [h2v]
  have hq : (1 : ℝ) ≤ D.host.q := by exact_mod_cast D.host.hyp.1.one_lt.le
  have hd : (1 : ℝ) ≤ D.host.d := by exact_mod_cast D.host.hyp.2.1.one_lt.le
  have hn : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have ht : (1 : ℝ) ≤ D.R.t := hT.1
  have hqd : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d := by
    have h1 : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hcond : D.host.rdE ≤ Formalism.MainNotions.szCond large₂ := by
    unfold Formalism.MainNotions.szCond
    calc D.host.rdE ≤ (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d) := hr2
      _ ≤ (D.host.QS : ℝ) / 2 * ((D.host.q : ℝ) * D.host.d) := by gcongr
      _ ≤ (D.host.QS : ℝ) * D.host.q * D.host.d := by
        have h0 : (0 : ℝ) ≤ (D.host.QS : ℝ) * ((D.host.q : ℝ) * D.host.d) := by positivity
        nlinarith
  have hc1 : (1 : ℝ) ≤ Formalism.MainNotions.szCond large₂ := le_trans hr1 hcond
  have hb0 : 0 < large₂.sc.b := lt_of_lt_of_le (by norm_num) (Formalism.MainNotions.S.two_le_scb large₂)
  have h36 : Formalism.MainNotions.szCond large₂ ^ 36 ≤ Real.sqrt large₂.sc.b := by
    have : Formalism.MainNotions.szCond large₂ ^ 36 ≤ Formalism.MainNotions.szCond large₂ ^ 36 * (D.R.t : ℝ) ^ 150 := by
      have : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ ht
      nlinarith [pow_pos (lt_of_lt_of_le one_pos hc1) 36]
    exact this.trans hC
  have hl := Real.log_le_log (pow_pos (lt_of_lt_of_le one_pos hc1) 36) h36
  rw [Real.log_pow, Real.log_sqrt hb0.le] at hl
  have hl2 := Real.log_le_log (lt_of_lt_of_le one_pos hr1) hcond
  push_cast at hl
  linarith

theorem eN_le (D : D7) : eN D ≤ (D.R.m : ℝ) ^ 2 / 2 := by
  unfold eN
  have h : (D.R.rS : ℝ) ≤ (D.R.m : ℝ) / 2 := by
    have : 2 * D.R.rS ≤ D.R.m := by unfold Formalism.BasicNotions.Ranks.rS; omega
    have : (2 * D.R.rS : ℝ) ≤ D.R.m := by exact_mod_cast this
    linarith
  have h0 : (0 : ℝ) ≤ D.R.rS := by positivity
  have hm : (1 : ℝ) ≤ D.R.m := by have := D.R.two_le_m; exact_mod_cast (by omega : 1 ≤ D.R.m)
  nlinarith

theorem covWinN_sizes (hF : CovNFormula) {D : D7} {X : HidaSetting D} {Y : Full X} (C : Choice X 1) (large₂ : SizeData₂ D)
    (hS : Formalism.MainNotions.SizesAt large₂) {C1 : ℝ} (hC1 : 1 / 144 ≤ C1) (u u' : D.what₂.Word) :
    LoopTerm.CovWinN (Y := Y) C large₂ C1 u u' := by
  have hv := rdE_ge_one D
  have hl0 : 0 ≤ Real.log (2 * D.host.v) := Real.log_nonneg hv
  have hl := log_rd_le large₂ hS
  have he := eN_le D
  have hb : 0 ≤ Real.log large₂.sc.b := by linarith
  have hm : 0 ≤ (D.R.m : ℝ) ^ 2 := by positivity
  refine covWinN_of hF C large₂ (by linarith) ?_ u u'
  calc eN D * Real.log (2 * D.host.v) ≤ ((D.R.m : ℝ) ^ 2 / 2) * (Real.log large₂.sc.b / 72) :=
        mul_le_mul he hl hl0 (by positivity)
    _ = 1 / 144 * (D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b := by ring
    _ ≤ C1 * (D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b := by
        apply mul_le_mul_of_nonneg_right _ hb
        exact mul_le_mul_of_nonneg_right hC1 hm

theorem covN_pos (hF : CovNFormula) {D : D7} {X : HidaSetting D} {Y : Full X} {θ : ℝ} (hθ : 0 < θ) (C : Choice X θ)
    (u u' : D.what₂.Word) : 0 < LoopTerm.covN (Y := Y) C u * LoopTerm.covN (Y := Y) C u' := by
  rw [hF D X Y θ C u hθ, hF D X Y θ C u' hθ]
  have h1 := rdE_ge_one D
  have h2 : 0 < θ * (2 * D.host.v) ^ eN D := mul_pos hθ (Real.rpow_pos_of_pos (by linarith) _)
  exact mul_pos (pow_pos h2 _) (pow_pos h2 _)

end Formalism.L2.SG.Pf.LoopBCovN
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

def cutStd : Formalism.FourierDecayAlt.LE.Cut where
  χ := chiStd
  smooth := isCut0_chiStd.1
  zero x hx := Real.smoothTransition.zero_of_nonpos (by linarith)
  one x hx := Real.smoothTransition.one_of_one_le (by linarith)
  nonneg _ := Real.smoothTransition.nonneg _
  le_one _ := Real.smoothTransition.le_one _

theorem isCut0_cut (c : Formalism.FourierDecayAlt.LE.Cut) : Formalism.FourierDecayAlt.C6.IsCut0 c.χ :=
  ⟨c.smooth, ⟨1 / 2, by norm_num, fun x hx => c.zero x hx.le⟩, c.one⟩

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)

abbrev parE (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (u u' : D.what₂.Word) (de de' : ℕ → ℝ) (j : Fin (nfE D)) :
    Formalism.FourierDecayAlt.M.Par :=
  ⟨D.R.k, D.R.rS, ((D.mem u).A.T : ℝ), ((D.mem u').A.T : ℝ),
    ((Formalism.L2.SG.SpectralTiesReal.gOf D e).place (plE D j)).u de, ((Formalism.L2.SG.SpectralTiesReal.gOf D e).place (plE D j)).u de'⟩

def carrierInT (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ) : CarrierIn X u u' :=
  carrierIn X C u u' e he hv CA de de' l grid grid1 fc c.χ
    (sgOf (Formalism.L2.SG.SpectralTiesReal.gOf D e) (plE D) ((D.mem u).A.T : ℝ) ((D.mem u').A.T : ℝ) de de' (l + 1)) ν' m₀
    (fun j => Formalism.FourierDecayAlt.Top.topOf (parE e u u' de de' j) (l + 1) (towersOf X C u u' e j) (ν' j) (m₀ j) (Θ j) (TP j)) A₀

end Formalism.L2.SG.Pf.CarrierT
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf.BDat Formalism.L2.SG.Pf.JointAmplitudePoints Formalism.L2.SG.Pf.ThmBChain Formalism.L2.SG.RealObj
open scoped ENNReal

namespace Formalism.L2.SG.Pf.OOCore3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section K

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (ν : X.B.I.Ginf → Measure X.B.I.Ginf)
  {θ : ℝ} (C : Choice X θ) (hB : WuBessel C) (large₂ : SizeData₂ D) (C1 : ℝ)

def sclV : ℝ :=
  Complex.normSq ((Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ)

def WinK (K : ℝ) : Prop := normWin D large₂ C1 (K ^ ((1 : ℝ) / (2 * Fintype.card D.what₂.Tau)))

def OOCorePK : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    (∃ g, IsPtRep X u u' w g) →
    ∃ K : ℝ, 0 < K ∧ WinK large₂ C1 K ∧
      sclV Y u u' * Formalism.MainNotions.S.hsNormSq (Formalism.L2.SG.Pf.OOCore.OOP u u' ν w) * K = localAmplitudeProduct u u' hB w

def JFactPK : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    0 < J2of Y u u' ν (toPts w) →
    ∃ K : ℝ, 0 < K ∧ WinK large₂ C1 K ∧ J2of Y u u' ν (toPts w) * K = localAmplitudeProduct u u' hB w

theorem jFactPK_of_core (h : OOCorePK Y u u' ν C hB large₂ C1) : JFactPK Y u u' ν C hB large₂ C1 := by
  intro w hb hJ
  obtain ⟨w', hw', g, hg⟩ := isPtRep_of_J2of hJ
  have hw'w : w' = w := toPts_injective hw'
  subst hw'w
  rw [Formalism.L2.SG.Pf.OOCore.joint_amplitude_eq_normSq Y u u' ν w' ⟨g, hg⟩]
  exact h w' hb ⟨g, hg⟩

theorem localAmplitudesPositive_of_kernel (h : JFactPK Y u u' ν C hB large₂ C1) : LocalAmplitudesPositive Y u u' ν C hB := by
  intro w hb hJ
  obtain ⟨K, hK, -, e⟩ := h w hb hJ
  rw [← e]
  exact mul_pos hJ hK

theorem thetaWinP_of_K (h : JFactPK Y u u' ν C hB large₂ C1) : ThetaWinP Y u u' ν C hB large₂ C1 := by
  intro w hb hJ
  obtain ⟨K, hK, hW, e⟩ := h w hb hJ
  have hP : 0 < localAmplitudeProduct u u' hB w := by rw [← e]; exact mul_pos hJ hK
  have e2 : thetaP u u' hB (J2of Y u u' ν (toPts w)) w = K ^ ((1 : ℝ) / (2 * Fintype.card D.what₂.Tau)) := by
    unfold thetaP
    rw [if_pos ⟨hJ, hP⟩, ← e, mul_div_cancel_left₀ _ hJ.ne']
  rw [e2]
  exact hW

def LocNormPK (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))) :
    Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    (∃ g, IsPtRep X u u' w g) →
    ∃ K : ℝ, 0 < K ∧ WinK large₂ C1 K ∧
      sclV Y u u' * (∏ v, Formalism.MainNotions.S.hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
        Jv (νl w v) (X.Wloc u v) (X.Wloc u' v) ((gamW X u u' w) v))) * K = localAmplitudeProduct u u' hB w

theorem ooCorePK_of (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)))
    (hQ : Formalism.L2.SG.Pf.Carrier.JointPf.OOQuot X u u' ν νl) (hN : LocNormPK Y u u' C hB large₂ C1 νl) :
    OOCorePK Y u u' ν C hB large₂ C1 := by
  intro w hb hw
  rw [Formalism.L2.SG.Pf.OOCoreHilbertSchmidt.hsNormSq_OOP_quot u u' ν νl hQ w hw (Formalism.L2.SG.Pf.OOCoreHilbertSchmidt.gxPos_holds u u' w hb hw)]
  exact hN w hb hw

end K

end Formalism.L2.SG.Pf.OOCore3
end
end
