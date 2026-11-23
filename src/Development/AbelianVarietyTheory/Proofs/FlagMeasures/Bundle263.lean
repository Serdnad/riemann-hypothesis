module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Formalism.PeriodIntegrals.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle223
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupProductMeasureIsHaar
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle092
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle047
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle042
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle246
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFibreFamilyEqAtContinuityPoint
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MeasurePreservingGlue
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle242
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoAverageL2Compact
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle247
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle211
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle212
public import Formalism.HermitianLattices.Bundle003
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Formalism.LocalRingCardinality.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle253
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle255
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle271
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle021
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
public import Formalism.HermitianLattices.HermitianLatticesProofs.MassTelescope
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff

@[expose] public section

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

variable {k r : ℕ}

theorem IsClosedSub.isMatGroup_of_unitary {S : Set (Mat k r)} (hS : IsClosedSub k r S) : PI.IsMatGroup S := by
  obtain ⟨hG, hcl, h1, hmul, hinv⟩ := hS
  refine ⟨hcl, h1, hmul, fun a ha => ⟨hinv a ha, ?_⟩⟩

  have e : aᴴ * Hpk k r * a = Hpk k r := hG ha
  have hH := Formalism.FourierDecayAlt.P.B2x2.hpk_unit k r
  have hd := congrArg Matrix.det e
  rw [Matrix.det_mul, Matrix.det_mul] at hd
  have hdet : IsUnit a.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, mul_zero] at hd
    exact hH.ne_zero hd.symm
  exact Matrix.mul_nonsing_inv a hdet

theorem map_invM_eq {S : Set (Mat k r)} (hS : PI.IsMatGroup S) {μ : Measure (Mt k r)}
    (hμ : IsHaarOn S μ) (hR : ∀ s ∈ S, μ.map (rmulM s) = μ) : μ.map invM = μ := by
  have hL : PI.IsHaarOnM S μ := hμ
  have hR' : PI.IsRightInvM S μ := hR
  ext B hB
  rw [Measure.map_apply measurable_invM hB]

  have h := GlobalTheory.HaarInversion.lintegral_inv_eq _ S μ hS hL hR' (B.indicator 1)
    (measurable_one.indicator hB)
  rw [lintegral_indicator_one hB] at h
  rw [← h, ← lintegral_indicator_one (measurable_invM hB)]
  rfl

theorem rightInv_of_multiple {S : Set (Mat k r)} (hS : PI.IsMatGroup S) {μ ν : Measure (Mt k r)}
    (hμ : IsHaarOn S μ) (hν : PI.IsHaarOnM S ν) (hR : PI.IsRightInvM S ν) :
    ∀ s ∈ S, μ.map (rmulM s) = μ := by
  intro s hs
  have hL : PI.IsHaarOnM S μ := hμ

  obtain ⟨c, -, -, hc⟩ := (GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ S ν hS hν).1 μ hL
  have hνs : ν.map (rmulM s) = ν := hR s hs
  rw [hc, Measure.map_smul, hνs]
  exact (continuous_rmulM s).measurable.aemeasurable

private theorem exists_isHaarOnM_of_isMatGroup {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : PI.IsMatGroup G) :
    ∃ μ : Measure (PI.MtM m), PI.IsHaarOnM G μ := by
  have he := GlobalTheory.MatHaar.inc_memb (G := G) (hG := hG)
  refine ⟨(GlobalTheory.MatHaar.haar0 hG).map GlobalTheory.MatHaar.inc, he.sigmaFinite_map, ?_, ?_, ?_⟩
  · intro h0
    rw [Measure.map_eq_zero_iff he.measurable.aemeasurable] at h0
    exact (NeZero.ne (GlobalTheory.MatHaar.haar0 hG)) h0
  · rw [he.map_apply]
    have : (GlobalTheory.MatHaar.inc (G := G) (hG := hG)) ⁻¹' {x | Matrix.of x ∉ G} = ∅ := by
      ext g
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact GlobalTheory.MatHaar.inc_mem g
    rw [this, measure_empty]
  · intro a ha
    let g0 : GlobalTheory.MatHaar.Grp G hG := ⟨a, ha⟩
    have hcomp : PI.lmulQ a ∘ GlobalTheory.MatHaar.inc (G := G) (hG := hG) =
        GlobalTheory.MatHaar.inc ∘ (fun g => g0 * g) := by
      funext g
      exact (GlobalTheory.MatHaar.inc_mul g0 g).symm
    rw [Measure.map_map (GlobalTheory.MatHaar.lmulQ_cont a).measurable he.measurable, hcomp,
      ← Measure.map_map he.measurable (measurable_const_mul g0), map_mul_left_eq_self]

theorem unimodular_S_N_UW : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z → ∀ μ : Measure (Mt k r), (IsHaarOn (Sset k r z) μ → IsUnimod (Sset k r z) μ) ∧ (IsHaarOn (Nset k r) μ → IsUnimod (Nset k r) μ ∧ ∀ h ∈ UWset k r z, μ.map (conjM h) = μ) ∧ (IsHaarOn (UWset k r z) μ → IsUnimod (UWset k r z) μ ∧ μ Set.univ < ⊤) := by
  intro k r z hz hT μ
  obtain ⟨-, hNc, hWc, -, -⟩ := closedSub_groups k r z hz hT
  have hN := hNc.isMatGroup_of_unitary
  have hW := hWc.isMatGroup_of_unitary
  obtain ⟨μN0, hμN0⟩ := exists_isHaarOnM_of_isMatGroup hN
  obtain ⟨μW0, hμW0⟩ := exists_isHaarOnM_of_isMatGroup hW
  refine ⟨fun hμ => ?_, fun hμ => ?_, fun hμ => ?_⟩
  ·
    obtain ⟨hSg, -, hSH, hSR⟩ := GlobalTheory.muSof_isHaar k r z μW0 μN0 hz hT hμW0 hμN0
    have hR := rightInv_of_multiple hSg hμ hSH hSR
    exact ⟨hR, map_invM_eq hSg hμ hR⟩
  · obtain ⟨-, -, hNR, -, hconj⟩ :=
      GlobalTheory.UnipotentRadicalHaar.unimodular_normal k r z μW0 μ hz hT hμW0 hμ
    have hR : ∀ s ∈ Nset k r, μ.map (rmulM s) = μ := hNR
    exact ⟨⟨hR, map_invM_eq hN hμ hR⟩, fun h hh => hconj h hh⟩
  · obtain ⟨hWR, hfin, -, -, -⟩ :=
      GlobalTheory.UnipotentRadicalHaar.unimodular_normal k r z μ μN0 hz hT hμ hμN0
    have hR : ∀ s ∈ UWset k r z, μ.map (rmulM s) = μ := hWR
    exact ⟨⟨hR, map_invM_eq hW hμ hR⟩, measure_lt_top μ _⟩

end GlobalTheory.SgInf
end

section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

namespace GlobalTheory.GaussFibre

theorem eq_ofReal_deriv (G : ℝ → ℝ≥0∞) (F m : ℝ → ℝ) (β d : ℝ) (hβ : β ≠ 0)
    (hF : HasDerivAt F d β) (hm : ContinuousAt m 1) (hm1 : m 1 = 1)
    (hint : ∀ a b : ℝ, a ≤ b → (0 : ℝ) ∉ Set.Ioc a b →
      ∫⁻ y in Set.Ioc a b, G y = ENNReal.ofReal (F b - F a))
    (hup : ∀ t, 1 ≤ t → G (t * β) ≤ ENNReal.ofReal (m t) * G β)
    (hlo : ∀ t, 0 < t → t ≤ 1 → ENNReal.ofReal (m t) * G β ≤ G (t * β)) :
    G β = ENNReal.ofReal d := by
  have hsl : Tendsto (fun t : ℝ => ENNReal.ofReal (slope F β (t * β))) (𝓝[≠] 1)
      (𝓝 (ENNReal.ofReal d)) := by
    refine (ENNReal.continuous_ofReal.tendsto d).comp
      ((hasDerivAt_iff_tendsto_slope.1 hF).comp ?_)
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => t * β) (𝓝 1) (𝓝 (1 * β)) :=
        (continuous_id.mul continuous_const).tendsto 1
      rw [one_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht h
      exact ht (mul_right_cancel₀ hβ ((h : t * β = β).trans (one_mul β).symm))
  have hmem : ∀ t y, y ∈ Set.uIoc β (t * β) → ∃ s ∈ Set.uIcc 1 t, s * β = y := by
    intro t y hy
    have h1 := Set.uIoc_subset_uIcc hy
    have h2 := Set.image_mul_const_uIcc β 1 t
    rw [one_mul] at h2
    rw [← h2] at h1
    exact h1
  have hI : ∀ t, 0 < t → t ≠ 1 → ∫⁻ y in Set.uIoc β (t * β), G y =
      ENNReal.ofReal (slope F β (t * β)) * volume (Set.uIoc β (t * β)) := by
    intro t ht ht1
    have h0 : (0 : ℝ) ∉ Set.uIoc β (t * β) := by
      intro h
      obtain ⟨s, hs, hs0⟩ := hmem t 0 h
      have : 0 < s := lt_of_lt_of_le (lt_min one_pos ht) hs.1
      exact (mul_ne_zero this.ne' hβ) hs0
    have hne : t * β - β ≠ 0 := by
      intro h
      exact ht1 (mul_right_cancel₀ hβ ((sub_eq_zero.1 h).trans (one_mul β).symm))
    rw [Real.volume_uIoc, ← ENNReal.ofReal_mul' (abs_nonneg _), slope_def_field]
    rcases le_total β (t * β) with h | h
    · rw [Set.uIoc_of_le h] at h0 ⊢
      rw [hint _ _ h h0, abs_of_nonneg (sub_nonneg.2 h), div_mul_cancel₀ _ hne]
    · rw [Set.uIoc_of_ge h] at h0 ⊢
      rw [hint _ _ h h0, abs_of_nonpos (sub_nonpos.2 h), mul_neg, div_mul_cancel₀ _ hne, neg_sub]
  have hv0 : ∀ t, t ≠ 1 → volume (Set.uIoc β (t * β)) ≠ 0 := by
    intro t ht1
    have hne : t * β - β ≠ 0 := by
      intro h
      exact ht1 (mul_right_cancel₀ hβ ((sub_eq_zero.1 h).trans (one_mul β).symm))
    rw [Real.volume_uIoc]
    exact (ENNReal.ofReal_pos.2 (abs_pos.2 hne)).ne'
  have hvt : ∀ t, volume (Set.uIoc β (t * β)) ≠ ⊤ := by
    intro t
    rw [Real.volume_uIoc]
    exact ENNReal.ofReal_ne_top
  have hev : ∀ p : ℝ → Prop, (∀ᶠ s in 𝓝 (1 : ℝ), p s) →
      ∀ᶠ t in 𝓝 (1 : ℝ), ∀ s ∈ Set.uIcc 1 t, p s := by
    intro p hp
    obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1 hp
    refine Metric.eventually_nhds_iff.2 ⟨δ, hδ, fun t ht s hs => h ?_⟩
    rw [Real.dist_eq] at ht ⊢
    exact (Set.abs_sub_left_of_mem_uIcc hs).trans_lt ht
  have hK : ∀ l : Filter ℝ, l ≤ 𝓝 1 →
      Tendsto (fun r : ℝ => ENNReal.ofReal r * G β) l (𝓝 (G β)) := by
    intro l hl
    have := ENNReal.Tendsto.mul_const (b := G β)
      ((ENNReal.continuous_ofReal.tendsto 1).mono_left hl) (Or.inl (by simp))
    simpa using this
  apply le_antisymm
  · refine le_of_tendsto (hK (𝓝[<] 1) nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : r < 1)
    refine ge_of_tendsto (hsl.mono_left (nhdsLT_le_nhdsNE 1)) ?_
    have h1 : ∀ᶠ s in 𝓝 (1 : ℝ), r < m s ∧ 0 < s :=
      (hm.eventually (lt_mem_nhds (hr.trans_eq hm1.symm))).and (lt_mem_nhds one_pos)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hev _ h1)] with t (ht : t < 1) hs
    rw [← ENNReal.mul_le_mul_iff_left (hv0 t ht.ne) (hvt t),
      ← hI t (hs t Set.right_mem_uIcc).2 ht.ne, ← setLIntegral_const]
    refine setLIntegral_mono' measurableSet_uIoc fun y hy => ?_
    obtain ⟨s, hs', rfl⟩ := hmem t y hy
    refine le_trans ?_ (hlo s (hs s hs').2 (hs'.2.trans (max_le le_rfl ht.le)))
    gcongr
    exact (hs s hs').1.le
  · refine ge_of_tendsto (hK (𝓝[>] 1) nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 1 < r)
    refine le_of_tendsto (hsl.mono_left (nhdsGT_le_nhdsNE 1)) ?_
    have h1 : ∀ᶠ s in 𝓝 (1 : ℝ), m s < r := hm.eventually (gt_mem_nhds (hm1.trans_lt hr))
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hev _ h1)] with t (ht : 1 < t) hs
    rw [← ENNReal.mul_le_mul_iff_left (hv0 t ht.ne') (hvt t),
      ← hI t (one_pos.trans ht) ht.ne', ← setLIntegral_const]
    refine setLIntegral_mono' measurableSet_uIoc fun y hy => ?_
    obtain ⟨s, hs', rfl⟩ := hmem t y hy
    refine le_trans (hup s ((le_min le_rfl ht.le).trans hs'.1)) ?_
    gcongr
    exact (hs s hs').le

variable {P Q : ℕ}

theorem gaussSp_pos (y : Sp P Q) : 0 < gaussSp y := Real.exp_pos _

theorem integrable_gaussSp : Integrable (gaussSp : Sp P Q → ℝ) := by
  have h1 : Integrable (fun z : ℂ => Real.exp (-‖z‖ ^ 2)) := by
    have := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := 1) (by simp) 0 0).norm
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp [Complex.norm_exp, ← Complex.ofReal_pow]
  have h2 := Integrable.fintype_prod (ι := Fin P ⊕ Fin Q) (μ := fun _ => (volume : Measure ℂ))
    (f := fun _ (z : ℂ) => Real.exp (-‖z‖ ^ 2)) (fun _ => h1)
  refine h2.congr (Eventually.of_forall fun y => ?_)
  simp only [gaussSp, ← Real.exp_sum, Finset.sum_neg_distrib]

theorem gaussSp_smul (c : ℝ) (y : Sp P Q) :
    gaussSp (c • y) = Real.exp (-(c ^ 2 * ∑ i, ‖y i‖ ^ 2)) := by
  simp only [gaussSp, Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Finset.mul_sum]

theorem shell {fib : ℝ → Measure (Sp P Q)} (h : IsDxDq fib) (a b : ℝ) (hab : a ≤ b)
    (h0 : (0 : ℝ) ∉ Set.Ioc a b) :
    ∫⁻ t in Set.Ioc a b, ∫⁻ y, ENNReal.ofReal (gaussSp y) ∂(fib t) =
      ENNReal.ofReal (2 ^ (P + Q) * (∫ y in {y : Sp P Q | qf y ≤ b}, gaussSp y) -
        2 ^ (P + Q) * ∫ y in {y : Sp P Q | qf y ≤ a}, gaussSp y) := by
  have hq : Measurable (qf : Sp P Q → ℝ) := GlobalTheory.RealPlaceCompare.continuous_qf.measurable
  have hO : MeasurableSet {x : Sp P Q | x ≠ 0} := isOpen_ne.measurableSet
  have hg : Measurable fun y : Sp P Q => ENNReal.ofReal (gaussSp y) :=
    ENNReal.measurable_ofReal.comp continuous_gaussSp.measurable
  have key := GlobalTheory.IsFibreFamily_lintegral_preimage hq isOpen_ne subset_rfl h
    (({x : Sp P Q | x ≠ 0}).indicator fun y => ENNReal.ofReal (gaussSp y)) (hg.indicator hO)
    (fun v hv => Set.indicator_of_notMem hv _) (Set.Ioc a b) measurableSet_Ioc
  have hsub : qf ⁻¹' Set.Ioc a b ⊆ {x : Sp P Q | x ≠ 0} := by
    rintro x hx rfl
    apply h0
    simpa [qf] using hx
  rw [Set.indicator_indicator, Set.inter_eq_left.2 hsub,
    lintegral_indicator (hq measurableSet_Ioc), Measure.restrict_restrict (hq measurableSet_Ioc),
    Set.inter_eq_left.2 hsub] at key
  have e0 : ∀ t, ∫⁻ y, ({x : Sp P Q | x ≠ 0}).indicator (fun y => ENNReal.ofReal (gaussSp y)) y
      ∂(fib t) = ∫⁻ y, ENNReal.ofReal (gaussSp y) ∂(fib t) := by
    intro t
    have h1 : ∀ᵐ y ∂(fib t), y ∈ qf ⁻¹' {id t} ∩ {x : Sp P Q | x ≠ 0} := h.1 t
    apply lintegral_congr_ae
    filter_upwards [h1] with y hy using Set.indicator_of_mem hy.2 _
  simp only [e0] at key
  have e1 : qf ⁻¹' Set.Ioc a b = {x : Sp P Q | qf x ≤ b} \ {x | qf x ≤ a} := by
    ext x; simp [and_comm]
  rw [← key, ← mul_sub, ← setIntegral_sdiff (s := {x : Sp P Q | qf x ≤ b})
      (t := {x : Sp P Q | qf x ≤ a}) (measurableSet_le hq measurable_const)
      integrable_gaussSp.integrableOn (fun x (hx : qf x ≤ a) => (hx.trans hab : qf x ≤ b)), ← e1,
    ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal integrable_gaussSp.integrableOn
      (Eventually.of_forall fun y => (gaussSp_pos y).le),
    dx, Measure.restrict_smul, lintegral_smul_measure, ENNReal.ofReal_pow (by norm_num)]
  simp

theorem gauss_fibre : ∀ (P Q : ℕ) (fib : ℝ → Measure (Sp P Q)) (β d : ℝ), IsDxDq fib → β ≠ 0 → HasDerivAt (fun t : ℝ => ∫ y in {y : Sp P Q | qf y ≤ t}, gaussSp y) d β → ∫⁻ y, ENNReal.ofReal (gaussSp y) ∂(fib β) = ENNReal.ofReal (2 ^ (P + Q) * d) := by
  intro P Q fib β d h hβ hF
  have hg : Measurable fun y : Sp P Q => ENNReal.ofReal (gaussSp y) :=
    ENNReal.measurable_ofReal.comp continuous_gaussSp.measurable
  refine eq_ofReal_deriv (fun t => ∫⁻ y, ENNReal.ofReal (gaussSp y) ∂(fib t)) _
    (fun t => t ^ (P + Q) / t) β _ hβ (hF.const_mul (2 ^ (P + Q) : ℝ))
    ((continuousAt_id.pow _).div continuousAt_id one_ne_zero) (by simp)
    (fun a b hab h0 => shell h a b hab h0) (fun t ht => ?_) (fun t ht ht1 => ?_)
  · have ht0 : 0 < t := one_pos.trans_le ht
    rw [GlobalTheory.T.lintegral_hermitianNormFibre_dilation P Q fib β t h hβ ht0 _ hg]
    gcongr with y
    rw [gaussSp_smul, Real.sq_sqrt ht0.le, gaussSp]
    have : 0 ≤ ∑ i, ‖y i‖ ^ 2 := by positivity
    exact Real.exp_le_exp.2 (by nlinarith)
  · rw [GlobalTheory.T.lintegral_hermitianNormFibre_dilation P Q fib β t h hβ ht _ hg]
    gcongr with y
    rw [gaussSp_smul, Real.sq_sqrt ht.le, gaussSp]
    have : 0 ≤ ∑ i, ‖y i‖ ^ 2 := by positivity
    exact Real.exp_le_exp.2 (by nlinarith)

end GlobalTheory.GaussFibre
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.ballMean_continuousLinearFunctional : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (σ : Mat k r → (H →L[ℂ] H)) (μG : Measure (Mt k r)) (T : H → Mat k r → Wp), IsHaarOn (GG k r) μG → (∀ u u' : H, (fun x : Mt k r => T (u + u') (Matrix.of x)) =ᵐ[μG] fun x => T u (Matrix.of x) + T u' (Matrix.of x)) → (∀ (b : ℂ) (u : H), (fun x : Mt k r => T (b • u) (Matrix.of x)) =ᵐ[μG] fun x => b • T u (Matrix.of x)) → (∀ K : Set (Mt k r), IsCompact K → ∃ C : ℝ, ∀ u : H, AEStronglyMeasurable (fun x : Mt k r => T u (Matrix.of x)) (μG.restrict K) ∧ ∫⁻ x in K, (‖T u (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μG ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) → (∀ y ∈ GG k r, ∀ u : H, (fun x : Mt k r => T (σ y u) (Matrix.of x)) =ᵐ[μG] fun x => T u (Matrix.of x * y)) → ∀ j : ℕ, ∃ Λ : H →L[ℂ] Wp, ∀ (v : H) (x : Mt k r), Matrix.of x ∈ GG k r → Λ (σ (Matrix.of x) v) = avgR μG j (fun z : Mt k r => T v (Matrix.of z)) x := by
  first | exact @GlobalTheory.SgInf.ballMean_clm | exact GlobalTheory.SgInf.ballMean_clm | (intros; apply GlobalTheory.SgInf.ballMean_clm <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.tendsto_average_L2_compact : ∀ (k r : ℕ) (μ : Measure (Mt k r)), IsHaarOn (GG k r) μ → ∀ {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (g : Mt k r → Wp), (∀ K : Set (Mt k r), IsCompact K → AEStronglyMeasurable g (μ.restrict K) ∧ ∫⁻ x in K, (‖g x‖₊ : ENNReal) ^ 2 ∂μ < ⊤) → ∀ K : Set (Mt k r), IsCompact K → Filter.Tendsto (fun j : ℕ => ∫⁻ x in K, (‖avgR μ j g x - g x‖₊ : ENNReal) ^ 2 ∂μ) Filter.atTop (nhds 0) := by
  first | exact @GlobalTheory.SgInf.tendsto_average_L2 | exact GlobalTheory.SgInf.tendsto_average_L2 | (intros; apply GlobalTheory.SgInf.tendsto_average_L2 <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConstBox

theorem local_vag {n d : ℕ} {ε : Fin n → Bool} {S : Set (Formalism.REAL.UJ ε)} {E : Fin d → Matrix (Fin n) (Fin n) ℂ}
    (h : IsCut ε S E) (μ : Measure (Formalism.REAL.UJ ε)) (hμ : IsGaugeSub S d μ) :
    SigmaFinite μ ∧ ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
      IsFiniteMeasure (μ.restrict {g | nrm (uMat g - 1) < t}) ∧
      Vag (μ.restrict {g | nrm (uMat g - 1) < t}) (fun g => crd E (uMat g - 1)) volume d := by
  obtain ⟨A, hA, hON, hspan, rfl⟩ := h
  obtain ⟨hσ, hcpt, -, r₀, hr₀, hlim⟩ := GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε A d E hA hON hspan μ hμ
  refine ⟨hσ, Real.sqrt r₀, Real.sqrt_pos.2 hr₀, fun t ht htt => ⟨?_, ?_⟩⟩
  ·
    refine isFiniteMeasure_restrict.2 (ne_of_lt ?_)
    refine lt_of_le_of_lt (measure_mono ?_) (isCompact_hsBall ε t).measure_lt_top
    intro g hg
    exact (show nrm (uMat g - 1) < t from hg).le
  ·
    intro φ hφ hsupp
    have hset : {g : Formalism.REAL.UJ ε | nrm (uMat g - 1) < t} =
        {g | Formalism.REAL.hs (uMat g - 1) < t ^ 2} := by
      ext g
      exact Real.sqrt_lt' ht
    have h1 : 0 < t ^ 2 := by positivity
    have h2 : t ^ 2 ≤ r₀ := by
      calc t ^ 2 ≤ Real.sqrt r₀ ^ 2 := pow_le_pow_left₀ ht.le htt 2
        _ = r₀ := Real.sq_sqrt hr₀.le
    rw [hset]
    refine (hlim (t ^ 2) h1 h2 φ hφ hsupp).congr (fun r => ?_)
    congr 2
    funext g
    congr 1
    ext i
    simp [crd, div_eq_mul_inv, mul_comm]

theorem prod_gauge_body : ∀ (n : ℕ) (ε : Fin n → Bool) (SN SM MainNotions : Set (Formalism.REAL.UJ ε)), ∀ (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ) (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ) (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ), IsCut ε SN EN → IsCut ε SM EM → IsCut ε MainNotions EK → (∀ v, gau EN EM EK EL v = 0 → v = 0) → ∀ μN μM μK : Measure (Formalism.REAL.UJ ε), IsGaugeSub SN dN μN → IsGaugeSub SM dM μM → IsGaugeSub MainNotions dK μK → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ → Filter.Tendsto (fun r : ℝ => (μN.prod (μM.prod μK)) {x | (nrm (uMat x.1 - 1) < t ∧ nrm (uMat x.2.1 - 1) < t ∧ nrm (uMat x.2.2 - 1) < t) ∧ gau EN EM EK EL (crd EN (uMat x.1 - 1), crd EM (uMat x.2.1 - 1), crd EK (uMat x.2.2 - 1)) ≤ r} / ENNReal.ofReal (r ^ (dN + (dM + dK)))) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (volume {v | gau EN EM EK EL v ≤ 1})) := by
  intro n ε SN SM MainNotions dN dM dK dL EN EM EK EL hN hM hK hgau μN μM μK hμN hμM hμK
  obtain ⟨hσN, tN, htN, hN'⟩ := local_vag hN μN hμN
  obtain ⟨hσM, tM, htM, hM'⟩ := local_vag hM μM hμM
  obtain ⟨hσK, tK, htK, hK'⟩ := local_vag hK μK hμK
  refine ⟨min tN (min tM tK), lt_min htN (lt_min htM htK), fun t ht htt => ?_⟩
  obtain ⟨fN, vN⟩ := hN' t ht (htt.trans (min_le_left _ _))
  obtain ⟨fM, vM⟩ := hM' t ht (htt.trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨fK, vK⟩ := hK' t ht (htt.trans ((min_le_right _ _).trans (min_le_right _ _)))
  set s : Set (Formalism.REAL.UJ ε) := {g | nrm (uMat g - 1) < t} with hs
  have hsm : MeasurableSet s := (continuous_nrm_uMat ε).measurable measurableSet_Iio
  have mc : ∀ {e : ℕ} (E : Fin e → Matrix (Fin n) (Fin n) ℂ),
      Measurable fun g : Formalism.REAL.UJ ε => crd E (uMat g - 1) :=
    fun E => (continuous_crd_uMat ε E).measurable

  have vMK := GlobalTheory.T.vague_limit_rescaled_measures_prod _ _ _ _ (μM.restrict s) (μK.restrict s) (fun g => crd EM (uMat g - 1))
    (fun g => crd EK (uMat g - 1)) volume volume dM dK (mc EM) (mc EK) vM vK
  have vNMK := GlobalTheory.T.vague_limit_rescaled_measures_prod _ _ _ _ (μN.restrict s) ((μM.restrict s).prod (μK.restrict s))
    (fun g => crd EN (uMat g - 1)) (Prod.map (fun g => crd EM (uMat g - 1)) (fun g => crd EK (uMat g - 1)))
    volume (volume.prod volume) dN (dM + dK) (mc EN) (Measurable.prodMap (mc EM) (mc EK)) vN vMK
  have h2 : (volume.prod volume : Measure ((Fin dM → ℝ) × (Fin dK → ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have h3 : (volume.prod (volume.prod volume) :
      Measure ((Fin dN → ℝ) × (Fin dM → ℝ) × (Fin dK → ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have key := GlobalTheory.T.tendsto_rescaled_measure_gauge_unit_body _ _ ((μN.restrict s).prod ((μM.restrict s).prod (μK.restrict s)))
    (Prod.map (fun g => crd EN (uMat g - 1))
      (Prod.map (fun g => crd EM (uMat g - 1)) (fun g => crd EK (uMat g - 1))))
    (volume.prod (volume.prod volume)) (dN + (dM + dK)) (gau EN EM EK EL)
    (Measurable.prodMap (mc EN) (Measurable.prodMap (mc EM) (mc EK))) (continuous_gau EN EM EK EL)
    (gau_nonneg EN EM EK EL) (fun c hc v => gau_smul EN EM EK EL c hc v) hgau vNMK
  refine key.congr (fun r => ?_)
  congr 1
  rw [Measure.prod_restrict, Measure.prod_restrict,
    Measure.restrict_apply' (hsm.prod (hsm.prod hsm))]
  congr 1
  ext ⟨a, b, c⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_prod, Prod.map_apply, hs]
  tauto

end GlobalTheory.IwConstBox
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.OrthoMass

theorem main : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∃ ms : ℕ → ℝ, (∀ n, 0 < ms n) ∧ ∀ (n : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (h : W →ₗ⋆[K] W →ₗ[K] K) (I : Submodule (𝓞 K) W), h.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h I n → Formalism.HermitianLatticesTheory.mass h I = ms n := by
  intro K _ _ _ hK
  refine ⟨fun n => Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm K n) (Formalism.MainNotions.StandardLattice.stdLat K n), fun n => ?_, ?_⟩
  · show 0 < Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm K n) (Formalism.MainNotions.StandardLattice.stdLat K n)
    rw [Formalism.MainNotions.StandardLattice.standard_form_eq_telescope_form, Formalism.MainNotions.StandardLattice.standard_lattice_eq_telescope_lattice]
    exact Formalism.HermitianLatticesTheory.massTelescope_std_pos K hK n
  · intro n W _ _ _ _ h I _ ho
    exact Formalism.MainNotions.StandardLattice.mass_ortho K hK n W h I ho

end GlobalTheory.OrthoMass
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.bessel_map_pairing_bound : Hyps → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (R : Rep D.R.k D.R.rS) (h : ℝ) (l : R.H → W.Wp) (l' : R.H → W.Wq) (dd : ℝ), cdScaleTie D → GoodW D τ w w' θ W → R.IsDS (epsSH D.R) lam → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z (psiS D W.z) R.σ W.π l → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z' (psiS D W.z') R.σ W.π' l' → 0 < dd → (∀ v ∈ R.sm, l2SG W.νS (fun g => l (R.σ g v)) = ENNReal.ofReal (‖v‖ ^ 2 / dd)) → (∀ v ∈ R.sm, l2SG W.νS' (fun g => l' (R.σ g v)) = ENNReal.ofReal (‖v‖ ^ 2 / dd)) → ∃ A : LocS W, GoodS D lam A := by
  first | exact @GlobalTheory.DatumOfPeriods.exists_goodS | exact GlobalTheory.DatumOfPeriods.exists_goodS | (intros; apply GlobalTheory.DatumOfPeriods.exists_goodS <;> assumption)
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.formal_degree_proportional : Hyps → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS), cdScaleTie D → GoodW D τ w w' θ W → ∃ κ : ℝ, 0 < κ ∧ ∀ (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), GoodS D lam A → ∀ v : A.H, v ≠ 0 → A.deg = κ * PI.BesselPeriodGGP.fdegH W.μG A.σ v ∧ 0 < A.deg := by
  first | exact @GlobalTheory.DegreeTie.deg_eq_mul_fdegH | exact GlobalTheory.DegreeTie.deg_eq_mul_fdegH | (intros; apply GlobalTheory.DegreeTie.deg_eq_mul_fdegH <;> assumption)
end
