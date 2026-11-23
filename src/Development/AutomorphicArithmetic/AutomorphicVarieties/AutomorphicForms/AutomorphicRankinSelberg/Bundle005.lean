module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory Set
open UpperHalfPlane hiding I

namespace UpperTheory.V.Af.Rs

private lemma strip_meas : MeasurableSet strip := by
  have hre : Continuous fun z : ℍ => z.re := Complex.continuous_re.comp UpperHalfPlane.continuous_coe
  exact (measurableSet_le measurable_const hre.measurable).inter
    (measurableSet_lt hre.measurable measurable_const)

private lemma pt_re (x y : ℝ) (hy : 0 < y) : (pt x y).re = x := by
  rw [pt, ← UpperHalfPlane.coe_re, UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using hy)]
  simp

private lemma vol_strip (hV : VolMap) :
    (volume : Measure ℍ).restrict strip = Measure.map (fun p : ℝ × ℝ => pt p.1 p.2)
      ((((volume : Measure ℝ).restrict (Ico 0 1)).prod (volume.restrict (Ioi 0))).withDensity
        fun p => ENNReal.ofReal (1 / p.2 ^ 2)) := by
  obtain ⟨hm, hv⟩ := hV
  have hS := hm strip_meas
  have h1 : ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0))) =
      ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict (univ ×ˢ Ioi 0) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have h2 : (fun p : ℝ × ℝ => pt p.1 p.2) ⁻¹' strip ∩ univ ×ˢ Ioi 0 = Ico 0 1 ×ˢ Ioi 0 := by
    ext ⟨x, y⟩
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, true_and, mem_Ioi, mem_Ico, strip,
      mem_setOf_eq]
    constructor
    · rintro ⟨h, hy⟩
      rw [pt_re x y hy] at h
      exact ⟨h, hy⟩
    · rintro ⟨h, hy⟩
      rw [pt_re x y hy]
      exact ⟨h, hy⟩
  rw [hv, Measure.restrict_map hm strip_meas, restrict_withDensity hS, h1,
    Measure.restrict_restrict hS, h2, Measure.prod_restrict]

end UpperTheory.V.Af.Rs

open UpperTheory.V.Af.Rs in
theorem UpperTheory.V.Af.Rs.stripFub :
    UpperTheory.V.Af.Rs.VolMap → UpperTheory.V.Af.Rs.StripFub := by
  intro hV H hH
  have hf : Measurable fun p : ℝ × ℝ => pt p.1 p.2 := hV.1
  have hg : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (1 / p.2 ^ 2) := by fun_prop
  have hlt : ∀ᵐ p ∂(((volume : Measure ℝ).restrict (Ico 0 1)).prod (volume.restrict (Ioi 0))),
      ENNReal.ofReal (1 / p.2 ^ 2) < ⊤ := Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hμ := vol_strip hV
  have hI : Integrable H ((volume : Measure ℍ).restrict strip) := hH
  rw [hμ] at hI
  have hHm := hI.1
  rw [integrable_map_measure hHm hf.aemeasurable,
    integrable_withDensity_iff_integrable_smul' hg hlt] at hI
  have hpt : ∀ p : ℝ × ℝ, (ENNReal.ofReal (1 / p.2 ^ 2)).toReal • (H ∘ fun p : ℝ × ℝ => pt p.1 p.2) p
      = ((1 / p.2 ^ 2 : ℝ) : ℂ) * H (pt p.1 p.2) := by
    intro p
    rw [ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
    rfl
  have hF : Integrable (fun p : ℝ × ℝ => ((1 / p.2 ^ 2 : ℝ) : ℂ) * H (pt p.1 p.2))
      (((volume : Measure ℝ).restrict (Ico 0 1)).prod (volume.restrict (Ioi 0))) :=
    hI.congr (Filter.Eventually.of_forall hpt)
  have hinner : ∀ y : ℝ, ∫ x, ((1 / y ^ 2 : ℝ) : ℂ) * H (pt x y) ∂(volume.restrict (Ico (0:ℝ) 1))
      = (∫ x in (0:ℝ)..1, H (pt x y)) / ((y ^ 2 : ℝ) : ℂ) := by
    intro y
    rw [integral_const_mul, intervalIntegral.integral_of_le zero_le_one,
      integral_Ico_eq_integral_Ioc, one_div, Complex.ofReal_inv, div_eq_inv_mul]
  refine ⟨?_, ?_⟩
  · have := hF.integral_prod_right
    simp only [hinner] at this
    exact this
  · calc ∫ z in strip, H z
        = ∫ p, H (pt p.1 p.2) ∂((((volume : Measure ℝ).restrict (Ico 0 1)).prod
            (volume.restrict (Ioi 0))).withDensity fun p => ENNReal.ofReal (1 / p.2 ^ 2)) := by
          rw [hμ, integral_map hf.aemeasurable hHm]
      _ = ∫ p, ((1 / p.2 ^ 2 : ℝ) : ℂ) * H (pt p.1 p.2) ∂(((volume : Measure ℝ).restrict (Ico 0 1)).prod
            (volume.restrict (Ioi 0))) := by
          rw [integral_withDensity_eq_integral_toReal_smul hg hlt]
          exact integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = ∫ y in Ioi 0, ∫ x, ((1 / y ^ 2 : ℝ) : ℂ) * H (pt x y) ∂(volume.restrict (Ico (0:ℝ) 1)) :=
          integral_prod_symm _ hF
      _ = _ := by simp only [hinner]
end

section

noncomputable section

open MeasureTheory Set
open UpperHalfPlane hiding I

namespace UpperTheory.V.Af.Rs

private lemma measurable_ofComplex : Measurable (ofComplex : ℂ → ℍ) := by
  classical
  rw [← measurableEmbedding_coe.measurable_comp_iff]
  have h : (UpperHalfPlane.coe ∘ (ofComplex : ℂ → ℍ)) =
      fun w : ℂ => if 0 < w.im then w else ((ofComplex 0 : ℍ) : ℂ) := by
    funext w
    by_cases hw : 0 < w.im
    · simp [hw, ofComplex_apply_of_im_pos hw]
    · simp only [Function.comp, hw, if_false]
      rw [ofComplex_apply_of_im_nonpos (not_lt.mp hw), ofComplex_apply_of_im_nonpos (le_refl _ : (0 : ℂ).im ≤ 0)]
  rw [h]
  exact Measurable.ite (measurableSet_lt measurable_const Complex.measurable_im) measurable_id measurable_const

private lemma pt_eq (p : ℝ × ℝ) : pt p.1 p.2 = ofComplex (Complex.measurableEquivRealProd.symm p) := by
  unfold pt
  congr 1
  apply Complex.ext <;> simp

theorem volMap : VolMap := by
  have hm : Measurable (fun p : ℝ × ℝ => pt p.1 p.2) := by
    simp only [pt_eq]
    exact measurable_ofComplex.comp Complex.measurableEquivRealProd.symm.measurable
  refine ⟨hm, ?_⟩
  ext s hs
  have hp : (volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ))) =
      (volume : Measure (ℝ × ℝ)).restrict (univ ×ˢ Ioi 0) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hset : (fun p : ℝ × ℝ => pt p.1 p.2) ⁻¹' s ∩ univ ×ˢ Ioi 0 =
      Complex.measurableEquivRealProd.symm ⁻¹' (UpperHalfPlane.coe '' s) := by
    ext p
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, true_and, mem_Ioi, mem_image, pt_eq]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : 0 < (Complex.measurableEquivRealProd.symm p).im := by simpa using h2
      refine ⟨_, h1, ?_⟩
      rw [ofComplex_apply_of_im_pos h3]
    · rintro ⟨z, hz, hzp⟩
      refine ⟨?_, ?_⟩
      · rw [← hzp, ofComplex_apply]; exact hz
      · have h3 : 0 < (Complex.measurableEquivRealProd.symm p).im := by
          rw [← hzp]; exact z.im_pos
        simpa using h3
  rw [Measure.map_apply hm hs, withDensity_apply _ (hm hs), hp, Measure.restrict_restrict (hm hs), hset,
    volume_eq_lintegral,
    ← (Complex.volume_preserving_equiv_real_prod.symm _).setLIntegral_comp_preimage_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding]
  refine lintegral_congr fun p => ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  simp

end UpperTheory.V.Af.Rs
end
end

section

open MeasureTheory Set
open UpperHalfPlane hiding I

private theorem pt_re_im (x y : ℝ) (hy : 0 < y) :
    (UpperTheory.V.Af.Rs.pt x y).re = x ∧ (UpperTheory.V.Af.Rs.pt x y).im = y := by
  rw [UpperTheory.V.Af.Rs.pt, ← UpperHalfPlane.coe_re, ← UpperHalfPlane.coe_im,
    UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using hy)]
  simp

private theorem measurableSet_strip' : MeasurableSet UpperTheory.V.Af.Rs.strip := by
  have hre : Continuous fun z : ℍ => z.re := Complex.continuous_re.comp UpperHalfPlane.continuous_coe
  exact (measurableSet_le measurable_const hre.measurable).inter
    (measurableSet_lt hre.measurable measurable_const)

private theorem volume_restrict_strip_eq_map_withDensity (hV : UpperTheory.V.Af.Rs.VolMap) :
    (volume : Measure ℍ).restrict UpperTheory.V.Af.Rs.strip =
      Measure.map (fun p : ℝ × ℝ => UpperTheory.V.Af.Rs.pt p.1 p.2)
      ((((volume : Measure ℝ).restrict (Ico 0 1)).prod (volume.restrict (Ioi 0))).withDensity
        fun p => ENNReal.ofReal (1 / p.2 ^ 2)) := by
  obtain ⟨hf, hvol⟩ := hV
  have hs : MeasurableSet ((fun p : ℝ × ℝ => UpperTheory.V.Af.Rs.pt p.1 p.2) ⁻¹' UpperTheory.V.Af.Rs.strip) :=
    hf measurableSet_strip'
  have hset : (fun p : ℝ × ℝ => UpperTheory.V.Af.Rs.pt p.1 p.2) ⁻¹' UpperTheory.V.Af.Rs.strip ∩ (univ ×ˢ Ioi 0)
      = Ico (0:ℝ) 1 ×ˢ Ioi 0 := by
    ext ⟨x, y⟩
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, true_and, mem_Ioi, mem_Ico,
      UpperTheory.V.Af.Rs.strip, mem_setOf_eq]
    constructor
    · rintro ⟨h, hy⟩
      rw [(pt_re_im x y hy).1] at h
      exact ⟨h, hy⟩
    · rintro ⟨h, hy⟩
      rw [(pt_re_im x y hy).1]
      exact ⟨h, hy⟩
  have h0 : (volume : Measure ℝ).prod (volume.restrict (Ioi (0:ℝ))) =
      ((volume : Measure ℝ).prod volume).restrict (univ ×ˢ Ioi 0) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hbase : ((volume : Measure ℝ).prod (volume.restrict (Ioi (0:ℝ)))).restrict
      ((fun p : ℝ × ℝ => UpperTheory.V.Af.Rs.pt p.1 p.2) ⁻¹' UpperTheory.V.Af.Rs.strip) =
      ((volume : Measure ℝ).restrict (Ico 0 1)).prod (volume.restrict (Ioi 0)) := by
    rw [h0, Measure.restrict_restrict hs, hset, ← Measure.prod_restrict]
  rw [hvol, Measure.restrict_map hf measurableSet_strip', restrict_withDensity hs, hbase]

theorem UpperTheory.V.Af.Rs.stripIm :
    UpperTheory.V.Af.Rs.VolMap → UpperTheory.V.Af.Rs.StripIm := by
  intro hV φ hφ hint
  have hf : Measurable fun p : ℝ × ℝ => UpperTheory.V.Af.Rs.pt p.1 p.2 := hV.1
  have hg : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (1 / p.2 ^ 2) := by fun_prop
  have hlt : ∀ᵐ p ∂(((volume : Measure ℝ).restrict (Ico 0 1)).prod (volume.restrict (Ioi 0))),
      ENNReal.ofReal (1 / p.2 ^ 2) < ⊤ := Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have him : Continuous fun z : ℍ => z.im := Complex.continuous_im.comp UpperHalfPlane.continuous_coe
  have hm : Measurable fun z : ℍ => φ z.im := hφ.comp him.measurable
  show Integrable (fun z : ℍ => φ z.im) ((volume : Measure ℍ).restrict UpperTheory.V.Af.Rs.strip)
  rw [volume_restrict_strip_eq_map_withDensity hV, integrable_map_measure hm.aestronglyMeasurable hf.aemeasurable,
    integrable_withDensity_iff_integrable_smul' hg hlt]
  have h1 : Integrable (fun _ : ℝ => (1:ℝ)) (volume.restrict (Ico (0:ℝ) 1)) := integrable_const 1
  have h2 : Integrable (fun y => φ y / y ^ 2) (volume.restrict (Ioi (0:ℝ))) := hint
  refine (h1.mul_prod h2).congr ?_
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioi)]
    with p hp
  simp only [Function.comp_apply, (pt_re_im p.1 p.2 hp).2,
    ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 1 / p.2 ^ 2), smul_eq_mul, one_mul]
  ring
end

section

open MeasureTheory Set in
private theorem UpperTheory.V.Af.Rs.line_null (c : ℝ) : volume {z : ℂ | z.re = c} = 0 := by
  have h : {z : ℂ | z.re = c} = Complex.measurableEquivRealProd ⁻¹' (({c} : Set ℝ) ×ˢ (univ : Set ℝ)) := by
    ext z
    simp
  rw [h, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv, Measure.volume_eq_prod,
    Measure.prod_prod]
  simp

open MeasureTheory Set in
theorem UpperTheory.V.Af.Rs.fdNull :
    UpperTheory.V.Af.Rs.VolMap → UpperTheory.V.Af.Rs.FdNull := by
  intro _
  unfold UpperTheory.V.Af.Rs.FdNull
  rw [UpperHalfPlane.volume_eq_lintegral]
  apply setLIntegral_measure_zero
  have h0 : volume (Metric.sphere (0 : ℂ) 1 ∪ ({z : ℂ | z.re = 1 / 2} ∪ {z : ℂ | z.re = -(1 / 2)})) = 0 :=
    measure_union_null (Measure.addHaar_sphere _ _ _)
      (measure_union_null (UpperTheory.V.Af.Rs.line_null _) (UpperTheory.V.Af.Rs.line_null _))
  refine measure_mono_null ?_ h0
  rintro _ ⟨z, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
  by_cases hs : 1 < Complex.normSq (z : ℂ)
  · right
    have h4 : ¬ |z.re| < 1 / 2 := fun h => h3 ⟨hs, h⟩
    have h5 : |z.re| = 1 / 2 := le_antisymm h2 (not_lt.mp h4)
    exact (abs_eq (by norm_num)).mp h5
  · left
    have h5 : Complex.normSq (z : ℂ) = 1 := le_antisymm (not_lt.mp hs) h1
    rw [Complex.normSq_eq_norm_sq] at h5
    rw [mem_sphere_zero_iff_norm]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h5
end

section

open MeasureTheory Set UpperHalfPlane
open scoped MatrixGroups ENNReal

private lemma UpperTheory.V.Af.Rs.unfM_mp (γ : SL(2, ℤ)) :
    MeasurePreserving (fun z : ℍ => γ • z) volume volume := by
  have : (fun z : ℍ => γ • z) = fun z : ℍ => ((γ : GL (Fin 2) ℝ)) • z := rfl
  rw [this]
  exact measurePreserving_smul _ _

theorem UpperTheory.V.Af.Rs.unfM :
    UpperTheory.V.Af.Rs.FdFin → UpperTheory.V.Af.Rs.FdCount → UpperTheory.V.Af.Rs.UnfM := by
  intro hFin hCount
  unfold UpperTheory.V.Af.Rs.UnfM
  unfold UpperTheory.V.Af.Rs.FdFin at hFin
  unfold UpperTheory.V.Af.Rs.FdCount at hCount
  obtain ⟨hfdm, -⟩ := hFin
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  haveI : Countable SL(2, ℤ) :=
    inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1})
  ext s hs
  rw [Measure.sum_apply _ hs]
  have step : ∀ γ : SL(2, ℤ), Measure.map (fun z : ℍ => γ • z) (volume.restrict ModularGroup.fd) s
      = ∫⁻ z in s, ModularGroup.fd.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • z) := by
    intro γ
    have hm : Measurable (fun z : ℍ => γ • z) := (UpperTheory.V.Af.Rs.unfM_mp γ).measurable
    have hm' : Measurable (fun z : ℍ => γ⁻¹ • z) := (UpperTheory.V.Af.Rs.unfM_mp γ⁻¹).measurable
    have hP : MeasurableSet ((fun z : ℍ => γ⁻¹ • z) ⁻¹' ModularGroup.fd) := hm' hfdm
    rw [Measure.map_apply hm hs, Measure.restrict_apply (hm hs)]
    have hind : (fun z : ℍ => ModularGroup.fd.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • z))
        = ((fun z : ℍ => γ⁻¹ • z) ⁻¹' ModularGroup.fd).indicator 1 := by
      ext z
      by_cases h : γ⁻¹ • z ∈ ModularGroup.fd
      · rw [indicator_of_mem h, indicator_of_mem (show z ∈ _ from h)]
        rfl
      · rw [indicator_of_notMem h, indicator_of_notMem (show z ∉ _ from h)]
    rw [hind, lintegral_indicator_one hP, Measure.restrict_apply hP,
      ← (UpperTheory.V.Af.Rs.unfM_mp γ).measure_preimage (hP.inter hs).nullMeasurableSet]
    congr 1
    ext z
    simp only [mem_preimage, mem_inter_iff, inv_smul_smul]
    exact and_comm
  rw [tsum_congr step]
  have hmeas : ∀ γ : SL(2, ℤ), AEMeasurable
      (fun z : ℍ => ModularGroup.fd.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • z))
      (volume.restrict s) := fun γ =>
    ((measurable_const.indicator hfdm).comp (UpperTheory.V.Af.Rs.unfM_mp γ⁻¹).measurable).aemeasurable
  rw [← lintegral_tsum hmeas]
  have hre : ∀ z : ℍ, ∑' γ : SL(2, ℤ), ModularGroup.fd.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • z)
      = ∑' γ : SL(2, ℤ), ModularGroup.fd.indicator (fun _ => (1 : ℝ≥0∞)) (γ • z) :=
    fun z => (Equiv.inv SL(2, ℤ)).tsum_eq
      (fun γ => ModularGroup.fd.indicator (fun _ => (1 : ℝ≥0∞)) (γ • z))
  simp_rw [hre]
  rw [lintegral_congr_ae (ae_restrict_of_ae hCount), setLIntegral_const, Measure.smul_apply]
  first
    | rw [two_mul, two_nsmul]
    | rw [smul_eq_mul]
    | simp [two_mul, two_smul]
end

section

open UpperTheory.V.Af.Rs in
private lemma gcdSum_inj :
    Function.Injective (fun p : ℕ × Cop => (((p.1 + 1 : ℕ) : ℤ)) • p.2.1) := by
  rintro ⟨n, a, ha⟩ ⟨m, b, hb⟩ h
  simp only at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Pi.smul_apply, smul_eq_mul] at h0 h1
  have ga : (a 0).gcd (a 1) = 1 := Int.isCoprime_iff_gcd_eq_one.mp ha
  have gb : (b 0).gcd (b 1) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hb
  have hk : (((n + 1 : ℕ) : ℤ) * a 0).gcd (((n + 1 : ℕ) : ℤ) * a 1)
      = (((m + 1 : ℕ) : ℤ) * b 0).gcd (((m + 1 : ℕ) : ℤ) * b 1) := by
    rw [h0, h1]
  rw [Int.gcd_mul_left, Int.gcd_mul_left, ga, gb] at hk
  simp only [Int.natAbs_natCast, mul_one] at hk
  have hnm : n = m := by omega
  subst hnm
  have hpos : ((n + 1 : ℕ) : ℤ) ≠ 0 := by positivity
  have e0 : a 0 = b 0 := mul_left_cancel₀ hpos h0
  have e1 : a 1 = b 1 := mul_left_cancel₀ hpos h1
  have hab : a = b := by
    funext i
    fin_cases i
    · exact e0
    · exact e1
  subst hab
  rfl

open UpperTheory.V.Af.Rs in
private lemma gcdSum_surj (v : Fin 2 → ℤ) (hv : v ≠ 0) :
    v ∈ Set.range (fun p : ℕ × Cop => (((p.1 + 1 : ℕ) : ℤ)) • p.2.1) := by
  set g := (v 0).gcd (v 1) with hg
  have hpos : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h0 | h
    · exfalso
      obtain ⟨a0, a1⟩ := Int.gcd_eq_zero_iff.mp h0
      apply hv
      funext i
      fin_cases i
      · exact a0
      · exact a1
    · exact h
  have hc : IsCoprime ((fun i => v i / (g : ℤ)) 0) ((fun i => v i / (g : ℤ)) 1) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd hpos)
  refine ⟨(g - 1, ⟨fun i => v i / (g : ℤ), hc⟩), ?_⟩
  have hg1 : g - 1 + 1 = g := Nat.sub_add_cancel hpos
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, hg1]
  fin_cases i
  · exact Int.mul_ediv_cancel' (Int.gcd_dvd_left (v 0) (v 1))
  · exact Int.mul_ediv_cancel' (Int.gcd_dvd_right (v 0) (v 1))

theorem UpperTheory.V.Af.Rs.gcdSum :
    UpperTheory.V.Af.Rs.GcdSum := by
  intro u c hu hc hu0 hc0 hmul
  have hsupp : Function.support u ⊆
      Set.range (fun p : ℕ × UpperTheory.V.Af.Rs.Cop => (((p.1 + 1 : ℕ) : ℤ)) • p.2.1) := by
    intro v hv
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact hv hu0
    exact gcdSum_surj v hv0
  rw [← gcdSum_inj.tsum_eq hsupp]
  have hterm : ∀ p : ℕ × UpperTheory.V.Af.Rs.Cop,
      u ((((p.1 + 1 : ℕ) : ℤ)) • p.2.1) = c (p.1 + 1) * u p.2.1 := fun p => hmul (p.1 + 1) p.2
  have hprod : Summable fun p : ℕ × UpperTheory.V.Af.Rs.Cop => c (p.1 + 1) * u p.2.1 := by
    have := hu.comp_injective gcdSum_inj
    refine this.congr fun p => ?_
    exact hterm p
  simp only [hterm]
  rw [hc.tsum_eq_zero_add, hc0, zero_add]
  exact ((hc.comp_injective (add_left_injective 1)).tsum_mul_tsum
    (hu.comp_injective Subtype.val_injective) hprod).symm
end

section

open MeasureTheory Set CongruenceSubgroup UpperTheory.V.Af UpperTheory.V.Sd
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm ComplexConjugate

private lemma UpperTheory.V.Af.Rs.upper_half_plane_point_im (x y : ℝ) (hy : 0 < y) : (UpperTheory.V.Af.Rs.pt x y).im = y := by
  unfold UpperTheory.V.Af.Rs.pt
  have him : 0 < ((x : ℂ) + y * Complex.I).im := by simp [hy]
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
  simp

theorem UpperTheory.V.Af.Rs.rankSum :
    UpperTheory.V.Af.Rs.StripFub → UpperTheory.V.Af.Rs.StripInt → UpperTheory.V.Af.Rs.NicePet → UpperTheory.V.Af.Rs.Pars → UpperTheory.V.Af.Rs.MelSum → UpperTheory.V.Af.Rs.RankSum := by
  intro hFub hInt hNice hPars hMel k L _ f s hs
  have hs1 : 1 < s := hs.1
  have hI := hInt _ (hNice k L f f) s hs
  obtain ⟨hY, -⟩ := hFub _ hI
  have hPa := hPars k L f f
  have hPsum : ∀ y, 0 < y → HasSum (fun n => ‖coef f n‖ ^ 2 * Real.exp (-(4 * Real.pi * n) * y))
      ((∫ x in (0 : ℝ)..1, conj (f (UpperTheory.V.Af.Rs.pt x y)) * f (UpperTheory.V.Af.Rs.pt x y)).re) := by
    intro y hy
    have h := Complex.reCLM.hasSum (hPa y hy)
    have e : (fun n => ‖coef f n‖ ^ 2 * Real.exp (-(4 * Real.pi * n) * y)) =
        fun n => Complex.reCLM (conj (coef f n) * coef f n * (Real.exp (-(4 * Real.pi * n) * y) : ℂ)) := by
      funext n
      rw [Complex.reCLM_apply, ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_mul,
        Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [e]
    simpa only [Complex.reCLM_apply] using h
  have hY2 : IntegrableOn (fun y : ℝ => ((∫ x in (0 : ℝ)..1,
      UpperHalfPlane.petersson (k : ℤ) f f (UpperTheory.V.Af.Rs.pt x y) *
        (((UpperTheory.V.Af.Rs.pt x y).im ^ s : ℝ) : ℂ)) / ((y ^ 2 : ℝ) : ℂ)).re) (Ioi 0) := hY.re
  have hIntP : IntegrableOn (fun y : ℝ =>
      (∫ x in (0 : ℝ)..1, conj (f (UpperTheory.V.Af.Rs.pt x y)) * f (UpperTheory.V.Af.Rs.pt x y)).re *
        y ^ ((k : ℝ) + s - 1 - 1)) (Ioi 0) := by
    refine hY2.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy' : 0 < y := hy
    have him : ∀ x, (UpperTheory.V.Af.Rs.pt x y).im = y := fun x => UpperTheory.V.Af.Rs.upper_half_plane_point_im x y hy'
    have hx : (∫ x in (0 : ℝ)..1, UpperHalfPlane.petersson (k : ℤ) f f (UpperTheory.V.Af.Rs.pt x y) *
        (((UpperTheory.V.Af.Rs.pt x y).im ^ s : ℝ) : ℂ)) =
        (∫ x in (0 : ℝ)..1, conj (f (UpperTheory.V.Af.Rs.pt x y)) * f (UpperTheory.V.Af.Rs.pt x y)) *
          ((y ^ k * y ^ s : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_mul_const]
      congr 1
      funext x
      simp [UpperHalfPlane.petersson, him, mul_assoc]
    dsimp only
    rw [hx, mul_div_assoc, ← Complex.ofReal_div, Complex.re_mul_ofReal]
    congr 1
    rw [show (k : ℝ) + s - 1 - 1 = ((k : ℝ) + s) - 2 by ring, Real.rpow_sub hy', Real.rpow_add hy',
      Real.rpow_natCast, Real.rpow_two]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  exact hMel (fun n => ‖coef f n‖ ^ 2) _ ((k : ℝ) + s - 1) (by linarith)
    (fun n => by positivity) hPsum hIntP
end
