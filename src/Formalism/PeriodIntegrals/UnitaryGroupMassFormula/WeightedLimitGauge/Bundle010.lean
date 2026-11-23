module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle007
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushH
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle009
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

variable {k : ℕ}

theorem lintegral_inv_smul {t : ℝ} (ht : 0 < t) {G : (Fin k → ℂ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ y, G (t⁻¹ • y) = ENNReal.ofReal (t ^ Module.finrank ℝ (Fin k → ℂ)) * ∫⁻ y, G y := by
  have hH : (volume : Measure (Fin k → ℂ)).IsAddHaarMeasure := inferInstance
  set f : (Fin k → ℂ) →ₗ[ℝ] (Fin k → ℂ) := t⁻¹ • LinearMap.id with hfdef
  have hdet : LinearMap.det f = (t⁻¹) ^ Module.finrank ℝ (Fin k → ℂ) := by
    rw [hfdef, LinearMap.det_smul, LinearMap.det_id, mul_one]
  have hdet0 : LinearMap.det f ≠ 0 := by rw [hdet]; exact pow_ne_zero _ (inv_ne_zero ht.ne')
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (Fin k → ℂ))) hdet0
  rw [hdet, inv_pow, inv_inv, abs_of_pos (pow_pos ht _)] at hmap
  have hfm : Measurable f := f.continuous_of_finiteDimensional.measurable
  have e : (fun y : Fin k → ℂ => G (t⁻¹ • y)) = fun y => G (f y) := by
    funext y
    simp [hfdef]
  rw [e, ← lintegral_map hG hfm, hmap, lintegral_smul_measure, smul_eq_mul]

theorem polar_symm_exp (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = (p.1 : ℂ) * Complex.exp (p.2 * Complex.I) := by
  rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem coneVol : ConeVol := by
  intro k T' hT'
  set d := Module.finrank ℝ (Fin k → ℂ) with hd
  set C : ℝ≥0∞ := ∫⁻ t in Set.Ioo (1 : ℝ) 2, ENNReal.ofReal (T' * t) * ENNReal.ofReal (t ^ d) with hC
  refine ⟨C, ?_, ?_, fun E hE => ?_⟩
  · apply ne_of_gt
    calc (0 : ℝ≥0∞) < ENNReal.ofReal T' * volume (Set.Ioo (1 : ℝ) 2) := by
          rw [Real.volume_Ioo]
          exact ENNReal.mul_pos (by simpa using hT') (by norm_num)
      _ = ∫⁻ t in Set.Ioo (1 : ℝ) 2, ENNReal.ofReal T' := (setLIntegral_const _ _).symm
      _ ≤ C := setLIntegral_mono' measurableSet_Ioo fun t ht => by
          have ht1 : 1 < t := ht.1
          rw [← ENNReal.ofReal_mul (by nlinarith)]
          apply ENNReal.ofReal_le_ofReal
          have h1 : 1 ≤ t ^ d := one_le_pow₀ ht1.le
          have h2 : 1 ≤ t * t ^ d := one_le_mul_of_one_le_of_one_le ht1.le h1
          calc T' = T' * 1 := (mul_one _).symm
            _ ≤ T' * (t * t ^ d) := mul_le_mul_of_nonneg_left h2 hT'.le
            _ = T' * t * t ^ d := by ring
  · apply ne_of_lt
    calc C ≤ ∫⁻ t in Set.Ioo (1 : ℝ) 2, ENNReal.ofReal (T' * 2 * 2 ^ d) :=
          setLIntegral_mono' measurableSet_Ioo fun t ht => by
            have ht1 : 1 < t := ht.1
            have ht2 : t < 2 := ht.2
            rw [← ENNReal.ofReal_mul (by nlinarith)]
            apply ENNReal.ofReal_le_ofReal
            have h1 : t ^ d ≤ 2 ^ d := pow_le_pow_left₀ (by linarith) ht2.le d
            have h2 : 0 ≤ t ^ d := pow_nonneg (by linarith) d
            have h3 : T' * t ≤ T' * 2 := by nlinarith
            calc T' * t * t ^ d ≤ T' * 2 * t ^ d := by nlinarith
              _ ≤ T' * 2 * 2 ^ d := by nlinarith
      _ < ⊤ := by
          rw [setLIntegral_const, Real.volume_Ioo]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hS := measurableSet_coneSh hT' hE
  have hf : Measurable (E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞)) := measurable_one.indicator hE
  set F3 : (Fin k → ℂ) → ℝ → ℝ → ℝ≥0∞ := fun y θ t =>
    ENNReal.ofReal (T' * t) * E.indicator 1 (hq k T' (t⁻¹ • y) θ) with hF3
  have hF3m : Measurable (fun p : ((Fin k → ℂ) × ℝ) × ℝ => F3 p.1.1 p.1.2 p.2) := by
    refine (ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_snd)).mul ?_
    exact hf.comp ((continuous_hq k T').measurable.comp
      ((measurable_snd.inv.smul (measurable_fst.comp measurable_fst)).prodMk (measurable_snd.comp measurable_fst)))

  have hfib : ∀ y : Fin k → ℂ, volume (Prod.mk y ⁻¹' coneSh k T' E) =
      ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, ∫⁻ t in Set.Ioo (1 : ℝ) 2, F3 y θ t := by
    intro y
    have hSy : MeasurableSet (Prod.mk y ⁻¹' coneSh k T' E) := measurable_prodMk_left hS
    have hg : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 •
        (Prod.mk y ⁻¹' coneSh k T' E).indicator (1 : ℂ → ℝ≥0∞) ((p.1 : ℂ) * Complex.exp (p.2 * Complex.I))) := by
      refine (ENNReal.measurable_ofReal.comp measurable_fst).smul ?_
      exact (measurable_one.indicator hSy).comp ((Complex.continuous_ofReal.comp continuous_fst).mul
        (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_snd).mul
          continuous_const))).measurable
    rw [← lintegral_indicator_one hSy, ← Complex.lintegral_comp_polarCoord_symm]
    simp_rw [polar_symm_exp]
    rw [polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hg.aemeasurable,
      lintegral_lintegral_swap hg.aemeasurable]
    refine lintegral_congr fun θ => ?_
    rw [hF3]
    dsimp only
    rw [← radial hT' E hE y θ]
    refine lintegral_congr fun R => ?_
    rw [smul_eq_mul]
    rfl
  rw [Measure.volume_eq_prod, Measure.prod_apply hS]
  simp_rw [hfib]

  have hm2 : Measurable (fun p : (Fin k → ℂ) × ℝ => ∫⁻ t in Set.Ioo (1 : ℝ) 2, F3 p.1 p.2 t) :=
    hF3m.lintegral_prod_right'
  rw [lintegral_lintegral_swap hm2.aemeasurable]
  have hm3 : ∀ θ : ℝ, Measurable (fun p : (Fin k → ℂ) × ℝ => F3 p.1 θ p.2) := fun θ =>
    hF3m.comp (((measurable_fst).prodMk measurable_const).prodMk measurable_snd)
  have step : ∀ θ : ℝ, ∫⁻ y, ∫⁻ t in Set.Ioo (1 : ℝ) 2, F3 y θ t =
      ∫⁻ t in Set.Ioo (1 : ℝ) 2, ENNReal.ofReal (T' * t) * ENNReal.ofReal (t ^ d) *
        ∫⁻ y, E.indicator 1 (hq k T' y θ) := by
    intro θ
    rw [lintegral_lintegral_swap (hm3 θ).aemeasurable]
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have ht0 : 0 < t := by linarith [ht.1]
    rw [hF3]
    dsimp only
    have hGm : Measurable (fun y : Fin k → ℂ => E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞) (hq k T' y θ)) :=
      hf.comp ((continuous_hq k T').measurable.comp (measurable_id.prodMk measurable_const))
    rw [lintegral_const_mul (ENNReal.ofReal (T' * t)) (f := fun x => E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞)
      (hq k T' (t⁻¹ • x) θ)) (hGm.comp (measurable_const_smul _))]
    have hsc := lintegral_inv_smul ht0 hGm
    rw [hsc, mul_assoc]
  simp_rw [step]
  have hP : Measurable (fun θ : ℝ => ∫⁻ y, E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞) (hq k T' y θ)) := by
    have : Measurable (fun p : (Fin k → ℂ) × ℝ => E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞) (hq k T' p.1 p.2)) :=
      hf.comp (continuous_hq k T').measurable
    exact this.lintegral_prod_left'
  have hct : Measurable (fun t : ℝ => ENNReal.ofReal (T' * t) * ENNReal.ofReal (t ^ d)) :=
    (ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_id)).mul
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const d))
  have hprod : Measurable (Function.uncurry fun (θ : ℝ) (t : ℝ) =>
      ENNReal.ofReal (T' * t) * ENNReal.ofReal (t ^ d) * ∫⁻ y, E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞) (hq k T' y θ)) :=
    (hct.comp measurable_snd).mul (hP.comp measurable_fst)
  rw [lintegral_lintegral_swap hprod.aemeasurable]
  unfold hqI
  rw [hC, ← lintegral_mul_const _ hct]
  refine lintegral_congr fun t => ?_
  rw [lintegral_const_mul _ hP]

end PI.RhsWLim.W
end
end

section

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal

namespace PI.RhsWLim.W.RI

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}

def GhatF (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW : Measure (Mt k r))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞) (ζ : ℂ) : ℝ≥0∞ :=
  Gf μW F (embWb k r (secP k r z z' μsec ζ) *ᵥ z')

theorem section_vector_properties (hd : WbData k r z z' μW μW' a a' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    inWb k r (embWb k r (μsec ζ) *ᵥ z') ∧
      herm (Hpk k r) (embWb k r (μsec ζ) *ᵥ z') (embWb k r (μsec ζ) *ᵥ z') = herm (Hpk k r) z' z' ∧
      herm (Hpk k r) (embWb k r (μsec ζ) *ᵥ z') z = ζ := by
  refine ⟨inWb_emb _ hd.z'_mem, herm_both _ _ (MB.emb_mem_UWb (hd.sec.2 ζ hζ).1).1 z' z', ?_⟩
  rw [PI.RhsWLim.W.ZetaZeros.herm_emb (μsec ζ) hd.z_mem hd.z'_mem]
  exact (hd.sec.2 ζ hζ).2

theorem meas_Ghat (hd : WbData k r z z' μW μW' a a' μsec) {F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞}
    (hF : Measurable F) : Measurable (GhatF k r z z' μW μsec F) := by
  have := hd.haarW.1
  have hc : Continuous (fun m : Fin (k + 1) → Fin (k + 1) → ℂ => embWb k r (Matrix.of m) *ᵥ z') :=
    (cont_emb.comp continuous_id).matrix_mulVec continuous_const
  exact (meas_Gf hF).comp (hc.measurable.comp (meas_secP hd.sec))

theorem orbInv_of (hQ : HypQ) (hU : UnimodK) (hT : FibTrans) : OrbInv := by
  intro k r z z' μW μW' a a' μsec hd s hs F hF
  have := hd.haarW.1
  have := hd.haarW'.1
  obtain ⟨Q, hσQ, hQi, hQc, c, hc0, hcT, hpol⟩ := hQ k r z z' hd.k_pos hd.z_mem hd.z'_mem hd.T_pos hd.T'_pos
  have hfinW : μW Set.univ ≠ ⊤ := by rw [hd.massW]; exact ENNReal.ofReal_ne_top
  have hnull : Q {v | Complex.normSq (herm (Hpk k r) v z) ≤ Tz k r z * Tz k r z'} = 0 := by
    have hS : MeasurableSet {ζ : ℂ | Complex.normSq ζ ≤ Tz k r z * Tz k r z'} :=
      measurableSet_le Complex.continuous_normSq.measurable measurable_const
    have h1 := hpol ({ζ : ℂ | Complex.normSq ζ ≤ Tz k r z * Tz k r z'}.indicator 1) (measurable_one.indicator hS)
    have e : (fun v => ({ζ : ℂ | Complex.normSq ζ ≤ Tz k r z * Tz k r z'}.indicator (1 : ℂ → ℝ≥0∞))
        (herm (Hpk k r) v z)) = ({v | Complex.normSq (herm (Hpk k r) v z) ≤ Tz k r z * Tz k r z'}).indicator 1 :=
      funext fun v => rfl
    have hmS : MeasurableSet {v | Complex.normSq (herm (Hpk k r) v z) ≤ Tz k r z * Tz k r z'} :=
      (cont_herm z).measurable hS
    rw [e, lintegral_indicator_one hmS] at h1
    rw [h1]
    have h2 : (fun ζ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) *
        {ζ : ℂ | Complex.normSq ζ ≤ Tz k r z * Tz k r z'}.indicator (1 : ℂ → ℝ≥0∞) ζ) =ᵐ[volume] 0 := by
      filter_upwards [circle_ae (Tz k r z * Tz k r z')] with ζ hζ
      show ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) *
        {ζ : ℂ | Complex.normSq ζ ≤ Tz k r z * Tz k r z'}.indicator (1 : ℂ → ℝ≥0∞) ζ = 0
      by_cases h : Complex.normSq ζ ≤ Tz k r z * Tz k r z'
      · have hlt : Complex.normSq ζ < Tz k r z * Tz k r z' := lt_of_le_of_ne h hζ
        have h0 : zWeight k (Tz k r z) (Tz k r z') ζ = 0 := by
          unfold zWeight
          rw [if_neg (not_le.2 hlt)]
        rw [h0, ENNReal.ofReal_zero, zero_mul]
      · simp only [Set.indicator, Set.mem_ofPred_eq, h, if_false, mul_zero]
    rw [lintegral_congr_ae h2, Pi.zero_def, lintegral_zero, mul_zero]
  have key : ∀ F' : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞, Measurable F' →
      c * rhsW k r z z' μW μW' μsec (fun x => F' (orbV k r z' x)) =
        ENNReal.ofReal a' * (ENNReal.ofReal a * ∫⁻ v, F' v ∂Q) := by
    intro F' hF'
    have sA : ∫⁻ ζ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * Gf μW F' (embWb k r (μsec ζ) *ᵥ z') =
        ∫⁻ ζ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * GhatF k r z z' μW μsec F' ζ := by
      refine lintegral_congr_ae ?_
      filter_upwards [circle_ae (Tz k r z * Tz k r z')] with ζ hζ
      by_cases h : Tz k r z * Tz k r z' < Complex.normSq ζ
      · unfold GhatF
        rw [secP_eq h]
      · have h0 : zWeight k (Tz k r z) (Tz k r z') ζ = 0 := by
          unfold zWeight
          rw [if_neg (not_le.2 (lt_of_le_of_ne (not_lt.1 h) hζ))]
        rw [h0, ENNReal.ofReal_zero, zero_mul, zero_mul]
    have sB : ∫⁻ v, GhatF k r z z' μW μsec F' (herm (Hpk k r) v z) ∂Q = ∫⁻ v, Gf μW F' v ∂Q := by
      refine lintegral_congr_ae ?_
      have hg1 : ∀ᵐ v ∂Q, inWb k r v ∧ herm (Hpk k r) v v = herm (Hpk k r) z' z' := by
        rw [ae_iff]
        exact hQc
      have hg2 : ∀ᵐ v ∂Q, Tz k r z * Tz k r z' < Complex.normSq (herm (Hpk k r) v z) := by
        rw [ae_iff]
        exact measure_mono_null (fun v (hv : ¬ (Tz k r z * Tz k r z' < _)) => not_lt.1 hv) hnull
      filter_upwards [hg1, hg2] with v hv1 hv2
      obtain ⟨p1, p2, p3⟩ := section_vector_properties hd hv2
      unfold GhatF
      rw [secP_eq hv2]
      exact Gf_fib hU hT hd.haarW hfinW hd.z_mem hd.T_pos hF' p1 hv1.1 (p2.trans hv1.2.symm) p3
    rw [rhs_orb hd F', sA, ← hd.massW, ← avg_Q Q hQi hd.haarW hF', ← sB, hpol _ (meas_Ghat hd hF')]
    ring
  have hmv : Measurable (fun v : Fin (2 * r + k + 1) → ℂ => s *ᵥ v) :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have k1 := key (fun v => F (s *ᵥ v)) (hF.comp hmv)
  have k2 := key F hF
  have eQ : ∫⁻ v, F (s *ᵥ v) ∂Q = ∫⁻ v, F v ∂Q := by
    rw [← lintegral_map hF hmv, hQi s hs]
  rw [eQ, ← k2] at k1
  exact (ENNReal.mul_right_inj hc0 hcT).1 k1

theorem rhsWInv_of_hyp (hQ : HypQ) (hU : UnimodK) (hT : FibTrans) : RhsWInv :=
  rhsWInv_of_orb (orbInv_of hQ hU hT)

end PI.RhsWLim.W.RI
end
end

section

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal

namespace PI.RhsWLim.W.RI

open PI.RhsWLim PI.RhsWLim.W

theorem fin_right {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [IsFiniteMeasure ν] [ν.IsMulLeftInvariant] (h0 : ν ≠ 0)
    (g : G) : ν.map (· * g) = ν := by
  have hg : Measurable (· * g : G → G) := measurable_mul_const g
  have hL : (ν.map (· * g)).IsMulLeftInvariant := by
    refine ⟨fun h => ?_⟩
    rw [Measure.map_map (measurable_const_mul h) hg]
    have e : ((h * ·) ∘ (· * g) : G → G) = (· * g) ∘ (h * ·) := funext fun x => (mul_assoc h x g).symm
    rw [e, ← Measure.map_map hg (measurable_const_mul h), map_mul_left_eq_self]
  have hU : (ν.map (· * g)) univ = ν univ := by
    rw [Measure.map_apply hg MeasurableSet.univ, preimage_univ]
  have hu0 : ν univ ≠ 0 := fun h => h0 (Measure.measure_univ_eq_zero.1 h)
  have hfin : IsFiniteMeasure (ν.map (· * g)) := inferInstance
  rw [measure_eq_div_smul (ν.map (· * g)) ν (s := univ) hu0 (measure_ne_top ν univ), hU,
    ENNReal.div_self hu0 (measure_ne_top ν univ), one_smul]

theorem unimodK : UnimodK := by
  intro k r z μ hW hfin b hb
  have : SigmaFinite μ := hW.1
  have hl := nuH_left hW
  have hmass : (μ.comap (jH z)) univ = μ univ := by
    conv_rhs => rw [← map_jH hW]
    rw [Measure.map_apply (jH_memb z).measurable MeasurableSet.univ, preimage_univ]
  have : IsFiniteMeasure (μ.comap (jH z)) := ⟨by rw [hmass]; exact lt_top_iff_ne_top.2 hfin⟩
  have h0 : μ.comap (jH z) ≠ 0 := by
    intro h
    apply hW.2.1
    rw [← map_jH hW, h, Measure.map_zero]
  have : SecondCountableTopology (stabH k r z) :=
    inferInstanceAs (SecondCountableTopology ((stabH k r z : Set (HU.Gp k r))))
  have : BorelSpace (stabH k r z) := inferInstanceAs (BorelSpace ((stabH k r z : Set (HU.Gp k r))))
  let g : stabH k r z := ⟨⟨fun i j => b i j, ⟨hb.1, hb.2.1⟩⟩, hb.2.2⟩
  have hR := fin_right (μ.comap (jH z)) h0 g
  have e : rmulM b ∘ jH z = jH z ∘ (· * g) := funext fun x => rfl
  calc μ.map (rmulM b) = ((μ.comap (jH z)).map (jH z)).map (rmulM b) := by rw [map_jH hW]
    _ = ((μ.comap (jH z)).map (· * g)).map (jH z) := by
        rw [Measure.map_map (rmulM_cont b).measurable (jH_memb z).measurable, e,
          ← Measure.map_map (jH_memb z).measurable (measurable_mul_const g)]
    _ = μ := by rw [hR, map_jH hW]

end PI.RhsWLim.W.RI
end
end
