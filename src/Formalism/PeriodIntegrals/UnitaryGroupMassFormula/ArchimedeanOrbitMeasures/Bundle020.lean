module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle017
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle014
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle018
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SdCoord
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle015
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle016
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SdTest
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.ProdFirstProjectionSmul
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
import Mathlib.RingTheory.PiTensorProduct
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle013

@[expose] public section

section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def JacOneCFor (Pr : ChartPred) : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a → Pr X u' hT μinf νinf a →
    ∀ Ω₂ ⊆ Ω, Ω₂ ∈ 𝓝 (TI X u' hT) → ∀ c : HmI X → ENNReal, ContinuousAt c (TI X u' hT) →
      PolId X u' μinf νinf a Ω₂ c → c (TI X u' hT) = (ENNReal.ofReal (KVal X u'))⁻¹

theorem jacOneCFor_of {Pr : ChartPred} (hK : KPos) (hR : LocRatioFor Pr) : JacOneCFor Pr := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hC hPr Ω₂ hΩ₂ hΩ₂n c hcc hid
  obtain ⟨V, W, hVW, hsh, hlim⟩ := hR X u' ψ hT μinf νinf fibInf hP Ω a hC hPr Ω₂ hΩ₂ hΩ₂n
  have hK0 : 0 < KVal X u' := hK X u' ψ hT μinf νinf fibInf hP
  set L : ℕ → ENNReal := fun n => μinf (BoxT X u' a (V n) (W n)) with hL
  set B : ℕ → ENNReal := fun n => νinf (W n) with hB
  set M : ℕ → ENNReal := fun n => X.measG.μGinf (TubeG X u' (V n)) with hM
  set A : ℕ → ENNReal := fun n => ∫⁻ T in W n, c T ∂νinf with hA

  have key : ∀ n, L n = A n * M n := by
    intro n
    obtain ⟨hWm, hWs, -, -, hU, hBm, hBI, -, hTm, -, hMt⟩ := hVW n
    have h := hid ((BoxT X u' a (V n) (W n)).indicator 1) (measurable_one.indicator hBm) (W n)
      hWs hWm
    have hsub : BoxT X u' a (V n) (W n) ⊆
        gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' (Subtype.val '' (W n)) ∩ IndI X := by
      intro y hy
      refine ⟨?_, hBI hy⟩
      obtain ⟨T, hTW, g, -, rfl⟩ := hy
      refine ⟨T, hTW, ?_⟩
      rw [gramR_smul, hC.2.2.2 T (hΩ₂ (hWs hTW))]
    rw [lintegral_indicator_one hBm, Measure.restrict_apply hBm, Set.inter_eq_left.2 hsub] at h
    have hin : ∀ T ∈ W n, ∫⁻ g, (BoxT X u' a (V n) (W n)).indicator 1 (g • rmulT X (a T) (Y0 X u'))
        ∂X.measG.μGinf = M n := by
      intro T hTW
      have hs := pre_box X u' hT hC (V n) (hWs.trans hΩ₂) hU T hTW
      have e : (fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J =>
          (BoxT X u' a (V n) (W n)).indicator (1 : TupI X → ENNReal) (g • rmulT X (a T) (Y0 X u'))) =
          (TubeG X u' (V n)).indicator 1 := by
        funext g
        by_cases hg : g ∈ TubeG X u' (V n)
        · have h4 : g • rmulT X (a T) (Y0 X u') ∈ BoxT X u' a (V n) (W n) := by rw [← hs] at hg; exact hg
          rw [Set.indicator_of_mem hg, Set.indicator_of_mem h4]; rfl
        · have h4 : g • rmulT X (a T) (Y0 X u') ∉ BoxT X u' a (V n) (W n) := by rw [← hs] at hg; exact hg
          rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem h4]
      rw [e, lintegral_indicator_one hTm]
    rw [setLIntegral_congr_fun hWm (fun T hT' => by rw [hin T hT'])] at h
    rw [lintegral_mul_const' _ _ hMt.ne] at h
    exact h
  have hAt : ∀ n, A n ≠ ⊤ := by
    intro n hA'
    obtain ⟨-, -, -, -, -, -, -, hLt, -, hM0, -⟩ := hVW n
    have : L n = ⊤ := by rw [key n, hA', ENNReal.top_mul hM0.ne']
    exact absurd this hLt.ne
  have e1 : ∀ n, (L n).toReal / ((B n).toReal * (M n).toReal) = (A n).toReal / (B n).toReal := by
    intro n
    obtain ⟨-, -, hB0, hBt, -, -, -, -, -, hM0, hMt⟩ := hVW n
    have hMr : 0 < (M n).toReal := ENNReal.toReal_pos hM0.ne' hMt.ne
    rw [key n, ENNReal.toReal_mul]
    field_simp
  have hlim' : Tendsto (fun n => (L n).toReal / ((B n).toReal * (M n).toReal)) atTop (𝓝 (KVal X u')⁻¹) := hlim

  have hge : ∀ b : ENNReal, b < c (TI X u' hT) → b.toReal ≤ (KVal X u')⁻¹ := by
    intro b hb
    have hU : c ⁻¹' Set.Ioi b ∈ 𝓝 (TI X u' hT) := hcc (Ioi_mem_nhds hb)
    refine ge_of_tendsto hlim' ?_
    filter_upwards [hsh _ hU] with n hn
    obtain ⟨hWm, -, hB0, hBt, -⟩ := hVW n
    have hBr : 0 < (B n).toReal := ENNReal.toReal_pos hB0.ne' hBt.ne
    have hlow : b * B n ≤ A n :=
      calc b * B n = ∫⁻ _ in W n, b ∂νinf := (setLIntegral_const _ _).symm
        _ ≤ A n := lintegral_mono_ae ((ae_restrict_iff' hWm).2 (Eventually.of_forall fun T hT' =>
            (hn hT').le))
    rw [e1 n, le_div_iff₀ hBr, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (hAt n) hlow

  have hle : ∀ b : ENNReal, c (TI X u' hT) < b → b ≠ ⊤ → (KVal X u')⁻¹ ≤ b.toReal := by
    intro b hb hbt
    have hU : c ⁻¹' Set.Iio b ∈ 𝓝 (TI X u' hT) := hcc (Iio_mem_nhds hb)
    refine le_of_tendsto hlim' ?_
    filter_upwards [hsh _ hU] with n hn
    obtain ⟨hWm, -, hB0, hBt, -⟩ := hVW n
    have hBr : 0 < (B n).toReal := ENNReal.toReal_pos hB0.ne' hBt.ne
    have hup : A n ≤ b * B n :=
      calc A n ≤ ∫⁻ _ in W n, b ∂νinf := lintegral_mono_ae ((ae_restrict_iff' hWm).2
            (Eventually.of_forall fun T hT' => (hn hT').le))
        _ = b * B n := setLIntegral_const _ _
    rw [e1 n, div_le_iff₀ hBr, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top hbt hBt.ne) hup

  have hfin : c (TI X u' hT) ≠ ⊤ := by
    intro htop
    have h1 := hge (ENNReal.ofReal ((KVal X u')⁻¹ + 1)) (by rw [htop]; exact ENNReal.ofReal_lt_top)
    rw [ENNReal.toReal_ofReal (by positivity)] at h1
    linarith
  set c₀ : ℝ := (c (TI X u' hT)).toReal with hc₀
  have hle' : c₀ ≤ (KVal X u')⁻¹ := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    by_cases hcε : c₀ - ε ≤ 0
    · have : 0 < (KVal X u')⁻¹ := inv_pos.2 hK0
      linarith
    · push_neg at hcε
      have hb : ENNReal.ofReal (c₀ - ε) < c (TI X u' hT) := by
        rw [← ENNReal.ofReal_toReal hfin, ← hc₀]
        exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
      have := hge _ hb
      rw [ENNReal.toReal_ofReal hcε.le] at this
      linarith
  have hge' : (KVal X u')⁻¹ ≤ c₀ := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hc0 : 0 ≤ c₀ := ENNReal.toReal_nonneg
    have hb : c (TI X u' hT) < ENNReal.ofReal (c₀ + ε) := by
      rw [← ENNReal.ofReal_toReal hfin, ← hc₀]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    have := hle _ hb ENNReal.ofReal_ne_top
    rwa [ENNReal.toReal_ofReal (by linarith)] at this
  have hceq : c₀ = (KVal X u')⁻¹ := le_antisymm hle' hge'
  rw [← ENNReal.ofReal_toReal hfin, ← hc₀, hceq, ENNReal.ofReal_inv_of_pos hK0]

theorem jacOneC_of_charts (hK : KPos) (hU : UnimodInf) (hW : WittNear) (hG : GoodChartEx) : JacOneC := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hC Ω₂ hΩ₂ hΩ₂n c hcc hid
  obtain ⟨Ω', a₂, hC₂, hgood⟩ := hG X u' ψ hT μinf νinf fibInf hP
  have hev : ∀ᶠ T in 𝓝 (TI X u' hT), ∃ h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J,
      rmulT X (a T) (Y0 X u') = h • rmulT X (a₂ T) (Y0 X u') := by
    obtain ⟨ι, _, κ, -, η, _, eT, eH, cμ, cν, Ψ', U, -, -, -, -, -, -, -, -, hev0, -⟩ := hgood
    filter_upwards [hev0, hC.1, hC₂.1] with T h1 h2 h3
    exact hW X u' ψ hT μinf νinf fibInf hP Ω a Ω' a₂ hC hC₂ T ⟨h2, h3⟩ h1.1
  set Ω₃ := Ω₂ ∩ Ω' ∩ {T | ∃ h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J,
      rmulT X (a T) (Y0 X u') = h • rmulT X (a₂ T) (Y0 X u')} with hΩ₃
  have hΩ₃n : Ω₃ ∈ 𝓝 (TI X u' hT) := inter_mem (inter_mem hΩ₂n hC₂.1) hev
  have hid₂ : PolId X u' μinf νinf a₂ Ω₃ c := by
    intro φ hφ S hS hSm
    rw [hid φ hφ S (hS.trans (Set.inter_subset_left.trans Set.inter_subset_left)) hSm]
    refine setLIntegral_congr_fun hSm (fun T hT' => ?_)
    obtain ⟨h, eh⟩ := (hS hT').2
    rw [eh]
    congr 1
    have e : ∀ g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J,
        φ (g • h • rmulT X (a₂ T) (Y0 X u')) = (fun g' => φ (g' • rmulT X (a₂ T) (Y0 X u'))) (g * h) := by
      intro g; simp only [mul_smul]
    simp_rw [e]
    exact hU X u' ψ hT μinf νinf fibInf hP (fun g' => φ (g' • rmulT X (a₂ T) (Y0 X u'))) h
  exact jacOneCFor_of hK (locRatioFor_of hK splitAsym_good) X u' ψ hT μinf νinf fibInf hP Ω' a₂ hC₂ hgood Ω₃
    (Set.inter_subset_left.trans Set.inter_subset_right) hΩ₃n c hcc hid₂

end PI.AprimeInfW
end
end

section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem wittNear_holds : WittNear := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a Ω' a₂ hC hC₂ T hTm hU
  obtain ⟨-, hmul, hsm, hgr, hcT, hc1, -, -⟩ := rmulFacts_holds X
  obtain ⟨u, hu⟩ := hU
  set w : TupI X := rmulT X (↑u⁻¹ : MfI X) (rmulT X (a T) (Y0 X u')) with hw
  have hgT : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (rmulT X (a T) (Y0 X u')) = (T : Matrix _ _ _) :=
    hC.2.2.2 T hTm.1
  have hgT₂ : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (rmulT X (a₂ T) (Y0 X u')) = (T : Matrix _ _ _) :=
    hC₂.2.2.2 T hTm.2
  have hY0 : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (Y0 X u') =
      (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F)) :=
    gramR_ratTup (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))
  have hinv1 : cTI X (↑u⁻¹ : MfI X) * cTI X (↑u : MfI X) = 1 := by
    rw [← hcT, Units.mul_inv, hc1]
  have hgw : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J w =
      (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F)) := by
    rw [hw, hgr, hgT, ← hgT₂, ← hu, hgr, hY0]
    rw [show cTI X (↑u⁻¹ : MfI X) * (cTI X (↑u : MfI X) *
        (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F)) * (↑u : MfI X)) *
        (↑u⁻¹ : MfI X) = (cTI X (↑u⁻¹ : MfI X) * cTI X (↑u : MfI X)) *
        (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F)) *
        ((↑u : MfI X) * (↑u⁻¹ : MfI X)) by simp only [Matrix.mul_assoc],
      hinv1, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
  have h2 : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  have hfix : ∀ b : X.B.I.E, X.B.I.cm.sig b = b ↔ b ∈ (algebraMap X.B.I.F X.B.I.E).range :=
    fun b => X.B.I.cm.fixed b
  have hinv : ∀ x, X.B.I.cm.sig (X.B.I.cm.sig x) = x := fun x => star_star x
  have hJ : IsHermND X.B.I.cm.sig X.B.I.J := by
    refine ⟨fun i j => ?_, X.B.I.J_det⟩
    have := congrFun (congrFun X.B.I.J_herm i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
    exact this
  have hdet := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  have hUC : PIW.AdelicOrbitU.UnitChoice (Ainf X.B.I.F) :=
    PIW.AdelicOrbitU.uc_pi (fun v : NumberField.InfinitePlace X.B.I.F => v.Completion)
  obtain ⟨g, hg⟩ := PI.AprimeInfWitt.witt_R X.B.I.cm.sig h2 hfix hinv X.B.I.J hJ (tupH (frameOf X u')) hT hdet
    (Ainf X.B.I.F) hUC w hgw
  refine ⟨g, ?_⟩
  have hback : rmulT X (↑u : MfI X) w = rmulT X (a T) (Y0 X u') := by
    rw [hw, hmul, Units.inv_mul, rmulT_one]
  rw [← hback, ← hu, hsm]
  congr 1
  exact hg.symm

end PI.AprimeInfW
end
end

section

noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

theorem totReal_of {D : D7} (X : HidaSetting D) : ∀ v : InfinitePlace X.B.I.F, v.IsReal :=
  fun v => X.B.I.cm.totReal.isReal v

def tupCoord {D : D7} (X : HidaSetting D) :
    TupI X ≃ₜ EuclideanSpace ℝ (Fin (D.R.rS + 1 + D.R.rS) × Fin X.B.I.n ×
      Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) × InfinitePlace X.B.I.F) :=
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  (Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ =>
    (tensCoord (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F)).trans
      (Homeomorph.piCongrRight fun _ => ainfReal (totReal_of X))).trans (flat4 _ _ _ _)

theorem tupCoord_add {D : D7} (X : HidaSetting D) (x y : TupI X) :
    tupCoord X (x + y) = tupCoord X x + tupCoord X y := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  simp only [tupCoord, Homeomorph.trans_apply]
  rw [← flatten_four_add]
  congr 1
  funext a i k
  simp only [Homeomorph.piCongrRight_apply, Homeomorph.trans_apply, Pi.add_apply]
  rw [tensCoord_add]
  exact ainfReal_add (totReal_of X) _ _

theorem psiInf_addP {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (a b : Ainf F) :
    psiInf F ψ (a + b) = psiInf F ψ a * psiInf F ψ b := by
  have h : (pairA F (a + b) 0 : AF F) = pairA F a 0 + pairA F b 0 := by
    show ((a + b, 0) : Ainf F × Af F) = ((a, 0) : Ainf F × Af F) + ((b, 0) : Ainf F × Af F)
    rw [Prod.mk_add_mk, add_zero]
  simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiInf]
  rw [h, AddChar.map_add_eq_mul]

theorem psiInf_eq {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hS : Formalism.L2.SG.LocVol.IsStdChar ψ) :
    psiInf F ψ = fun x => Complex.exp (2 * Real.pi * Complex.I *
      ((∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ)) :=
  funext hS

theorem continuous_psiInfP {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hS : Formalism.L2.SG.LocVol.IsStdChar ψ) : Continuous (psiInf F ψ) := by
  rw [psiInf_eq ψ hS]
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
  exact continuous_finsetSum _ fun w _ => Complex.continuous_re.comp
    ((InfinitePlace.Completion.isometry_extensionEmbedding (v := w)).continuous.comp (continuous_apply w))

theorem norm_psiInfP {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hS : Formalism.L2.SG.LocVol.IsStdChar ψ) (x : Ainf F) : ‖psiInf F ψ x‖ = 1 := by
  rw [hS x]
  have : 2 * (Real.pi : ℂ) * Complex.I *
      ((∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ) =
      ((2 * Real.pi * ∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ) *
        Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem BR_add_leftP {D : D7} (X : HidaSetting D) (x x' y : TupI X) :
    BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (x + x') y = BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y + BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x' y := by
  simp only [BR, hR, Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem BR_add_rightP {D : D7} (X : HidaSetting D) (x y y' : TupI X) :
    BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x (y + y') = BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y + BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y' := by
  simp only [BR, hR, Formalism.UG.hform, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem continuous_traceP {D : D7} (X : HidaSetting D) :
    Continuous (Algebra.trace (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  exact IsModuleTopology.continuous_of_linearMap _

theorem continuous_BR_leftP {D : D7} (X : HidaSetting D) (y : TupI X) : Continuous fun x : TupI X => BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  show Continuous fun x : TupI X => ∑ a, Algebra.trace (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)
    (∑ i, ∑ j, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Ainf X.B.I.F) X.B.I.cm.sig (x a i) * JR (Ainf X.B.I.F) X.B.I.J i j * y a j)
  exact continuous_finsetSum _ fun a _ => (continuous_traceP X).comp (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => (((continuous_sigRP (Ainf X.B.I.F) X.B.I.cm.sig).comp
      ((continuous_apply i).comp (continuous_apply a))).mul continuous_const).mul continuous_const)

theorem continuous_BR_rightP {D : D7} (X : HidaSetting D) (x : TupI X) : Continuous fun y : TupI X => BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  show Continuous fun y : TupI X => ∑ a, Algebra.trace (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)
    (∑ i, ∑ j, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Ainf X.B.I.F) X.B.I.cm.sig (x a i) * JR (Ainf X.B.I.F) X.B.I.J i j * y a j)
  exact continuous_finsetSum _ fun a _ => (continuous_traceP X).comp (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_apply j).comp (continuous_apply a)))

theorem sdTestI_holds : SdTestI := by
  intro D X u' ψ hT μinf νinf fibInf hP
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI := hP.2.2.2.2.1.1
  have hS := hP.2.2.1
  have hpc := continuous_psiInfP ψ hS
  exact ST.testEx_of_homeo μinf _ (tupCoord X) (tupCoord_add X)
    (fun x x' y => by rw [BR_add_leftP, psiInf_addP])
    (fun x y y' => by rw [BR_add_rightP, psiInf_addP])
    (fun x y => norm_psiInfP ψ hS _)
    (fun y => hpc.comp (continuous_BR_leftP X y))
    (fun x => hpc.comp (continuous_BR_rightP X x))

theorem invFib_holds : InvFib := invFib_of (sdInvG_of sdTestI_holds)

end PI.AprimeInfW
end
end
