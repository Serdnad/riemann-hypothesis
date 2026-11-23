module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasureB
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle004
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle006
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot locDens mInt MIntegrable ChartPartition integralWith)

theorem MIntMonoOfDensLe.proof : MIntMonoOfDensLe.Statement := by
  intro D X _ _ A V Φ Ψ hd g hg0 hgV hgi
  unfold mInt
  split_ifs with h
  · unfold integralWith
    refine Finset.sum_le_sum fun j _ => ?_
    have hTm := (A.chart j).open_target.measurableSet
    obtain ⟨hKc, hKs⟩ := ReciprocityTheory.AnForm.M.image_closed_compact (A.chart j)
      (isClosed_tsupport (h.some.χ j)) (h.some.tsupport_subset j)
    have hcc := ReciprocityTheory.AnForm.M.chi_comp_continuousOn h.some j
    have hint : IntegrableOn (fun y => h.some.χ j ((A.chart j).symm y) *
        g ((A.chart j).symm y) * locDens A Ψ j y) (A.chart j).target := by
      refine ReciprocityTheory.AnForm.M.integrableOn_target_of_closed (A.chart j)
        (Z := tsupport (h.some.χ j)) (fun y _ hy => by simp [image_eq_zero_of_notMem_tsupport hy]) ?_
      have h1 := (hgi j _ hKs hKc).mul_continuousOn (hcc.mono hKs) hKc
      exact h1.congr_fun (fun y _ => by ring) hKc.measurableSet
    refine integral_mono_of_nonneg (ae_restrict_of_forall_mem hTm fun y hy => ?_) hint
      (ae_restrict_of_forall_mem hTm fun y hy => ?_)
    · by_cases hyV : (A.chart j).symm y ∈ V
      · exact mul_nonneg (mul_nonneg (h.some.nonneg j _) (hg0 _)) (hd j y hy hyV).1
      · simp [hgV _ hyV]
    · by_cases hyV : (A.chart j).symm y ∈ V
      · exact mul_le_mul_of_nonneg_left (hd j y hy hyV).2 (mul_nonneg (h.some.nonneg j _) (hg0 _))
      · simp [hgV _ hyV]
  · exact le_rfl

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot locDens MIntegrable)

theorem MIntegrableOfDensLe.proof : MIntegrableOfDensLe.Statement := by
  intro D X _ A V Φ Ψ hV hΦc hΨc hle g hg hΨ j K hK hKc
  set e := A.chart j
  set dΦ := locDens A Φ j
  set dΨ := locDens A Ψ j
  have hO : IsOpen (e.target ∩ e.symm ⁻¹' V) := e.isOpen_inter_preimage_symm hV
  set W := (e.target ∩ e.symm ⁻¹' V) ∩ dΨ ⁻¹' Set.Ioi 0 with hWdef
  have hW : IsOpen W := (hΨc j).isOpen_inter_preimage hO isOpen_Ioi
  set q : (Fin D → ℂ) → ℝ := W.indicator (fun y => dΦ y / dΨ y) with hqdef
  have hqc : ContinuousOn (fun y => dΦ y / dΨ y) W :=
    ((hΦc j).mono Set.inter_subset_left).div ((hΨc j).mono Set.inter_subset_left)
      (fun y hy => (ne_of_gt hy.2))
  have hqm : AEStronglyMeasurable q (volume.restrict K) :=
    ((aestronglyMeasurable_indicator_iff hW.measurableSet).2
      (hqc.aestronglyMeasurable hW.measurableSet)).restrict
  have hqb : ∀ y, ‖q y‖ ≤ 1 := by
    intro y
    by_cases hy : y ∈ W
    · have hpos : 0 < dΨ y := hy.2
      obtain ⟨h0, h1⟩ := hle j y hy.1.1 hy.1.2
      rw [hqdef, Set.indicator_of_mem hy, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg h0 hpos.le)]
      exact (div_le_one hpos).2 h1
    · rw [hqdef, Set.indicator_of_notMem hy, norm_zero]
      exact zero_le_one
  have hint : IntegrableOn (fun y => (g (e.symm y) * dΨ y) * q y) K :=
    Integrable.mul_bdd (hΨ j K hK hKc) hqm (Filter.Eventually.of_forall hqb)
  refine hint.congr_fun ?_ hKc.measurableSet
  intro y hy
  have hyt : y ∈ e.target := hK hy
  simp only
  by_cases hyV : e.symm y ∈ V
  · obtain ⟨h0, h1⟩ := hle j y hyt hyV
    by_cases hpos : 0 < dΨ y
    · have hyW : y ∈ W := ⟨⟨hyt, hyV⟩, hpos⟩
      rw [hqdef, Set.indicator_of_mem hyW]
      field_simp
    · have hyW : y ∉ W := fun h => hpos h.2
      have hz : dΦ y = 0 := le_antisymm (h1.trans (not_lt.1 hpos)) h0
      rw [hqdef, Set.indicator_of_notMem hyW, hz]
      ring
  · rw [hg _ hyV]
    ring

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology
open ReciprocityTheory.AnForm (hessC)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh locDens mInt MIntegrable)

noncomputable section

variable {D : ℕ} {X : Type} [TopologicalSpace X]

theorem hessC_add_const_fun (f : (Fin D → ℂ) → ℝ) (c : ℝ) (z : Fin D → ℂ) :
    hessC (fun y => f y + c) z = hessC f z := by
  have h : fderiv ℝ (fun y => f y + c) = fderiv ℝ f := funext fun _ => fderiv_add_const c
  unfold hessC
  rw [h]

theorem locDens_potForm_congr (A : FinHolAtlas D X) (th : LocPot X) (u v : Fin D → X → ℝ)
    (W : Set X) (hW : IsOpen W) (j : Fin A.n) {y : Fin D → ℂ} (hy : y ∈ (A.chart j).target)
    (hyW : (A.chart j).symm y ∈ W) (hc : ∀ i, ∃ c : ℝ, ∀ x ∈ W, v i x = u i x + c) :
    locDens A (fun i => potForm th (v i)) j y = locDens A (fun i => potForm th (u i)) j y := by
  unfold ReciprocityTheory.AnForm.M.locDens
  refine ReciprocityTheory.AnForm.M.maDens_congr_hessC _ _ _ fun i => ?_
  obtain ⟨c, hc⟩ := hc i
  have hev : (fun y' => (potForm th (v i)).φ ((A.chart j).symm y) ((A.chart j).symm y')) =ᶠ[𝓝 y]
      fun y' => (potForm th (u i)).φ ((A.chart j).symm y) ((A.chart j).symm y') + c := by
    filter_upwards [((A.chart j).isOpen_inter_preimage_symm hW).mem_nhds ⟨hy, hyW⟩] with y' hy'
    show th.φ _ _ + v i _ = th.φ _ _ + u i _ + c
    rw [hc _ hy'.2]
    ring
  exact (ReciprocityTheory.AnForm.M.hessCGerm _ _ _ hev).trans (hessC_add_const_fun _ c y)

theorem measurableSet_chart_of_isOpen (A : FinHolAtlas D X) {S : Set X} (hS : IsOpen S) (j : Fin A.n) :
    MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) :=
  ((A.chart j).isOpen_inter_preimage_symm hS).measurableSet

theorem measurableSet_chart_diff (A : FinHolAtlas D X) {S S' : Set X} (j : Fin A.n)
    (hS : MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S))
    (hS' : MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S')) :
    MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (S \ S')) := by
  have h : (A.chart j).target ∩ (A.chart j).symm ⁻¹' (S \ S') =
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) \
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S') := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_sdiff]
    tauto
  rw [h]
  exact hS.diff hS'

theorem measurableSet_chart_compl (A : FinHolAtlas D X) {S : Set X} (j : Fin A.n)
    (hS : MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S)) :
    MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Sᶜ) := by
  have h : (A.chart j).target ∩ (A.chart j).symm ⁻¹' Sᶜ =
      (A.chart j).target \ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_sdiff]
    tauto
  rw [h]
  exact (A.chart j).open_target.measurableSet.diff hS

theorem mIntegrable_indicator (A : FinHolAtlas D X) (Ψ : Fin D → LocPot X)
    (hΨ : ∀ i, IsPotential A (Ψ i)) (S : Set X)
    (hS : ∀ j, MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S)) :
    MIntegrable A Ψ (S.indicator 1) := by
  intro j K hKt hK
  have h1 : IntegrableOn (locDens A Ψ j) K :=
    ((ReciprocityTheory.AnForm.M.locDensCont A Ψ hΨ j).mono hKt).integrableOn_compact hK
  refine (h1.indicator (hS j)).congr_fun (fun y hy => ?_) hK.measurableSet
  by_cases h : (A.chart j).symm y ∈ S
  · simp [h, hKt hy]
  · simp [h]

theorem mInt_indicator_union [CompactSpace X] [T2Space X] (A : FinHolAtlas D X)
    (Ψ : Fin D → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i)) (S S' : Set X)
    (hS : ∀ j, MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S))
    (hS' : ∀ j, MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S'))
    (hd : Disjoint S S') :
    mInt A Ψ ((S ∪ S').indicator 1) = mInt A Ψ (S.indicator 1) + mInt A Ψ (S'.indicator 1) := by
  have h := ReciprocityTheory.AnForm.M.mIntLinear A Ψ hΨ 1 _ _ (mIntegrable_indicator A Ψ hΨ S hS)
    (mIntegrable_indicator A Ψ hΨ S' hS')
  rw [one_mul] at h
  rw [← h]
  congr 1
  funext x
  rw [Set.indicator_union_of_disjoint hd, one_mul]

theorem mInt_one_split [CompactSpace X] [T2Space X] (A : FinHolAtlas D X)
    (Ψ : Fin D → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i)) (S : Set X)
    (hS : ∀ j, MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S)) :
    mInt A Ψ (fun _ => 1) = mInt A Ψ (S.indicator 1) + mInt A Ψ (Sᶜ.indicator 1) := by
  have h := mInt_indicator_union A Ψ hΨ S Sᶜ hS (fun j => measurableSet_chart_compl A j (hS j))
    disjoint_compl_right
  rw [Set.union_compl_self, Set.indicator_univ] at h
  exact h

theorem setIntegral_locDens_le_mInt [CompactSpace X] [T2Space X] (A : FinHolAtlas D X)
    (Ψ : Fin D → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i)) (hpsh : ∀ i, IsPsh A (Ψ i))
    (j : Fin A.n) (K : Set (Fin D → ℂ)) (hKt : K ⊆ (A.chart j).target) (hK : IsCompact K) :
    ∫ y in K, locDens A Ψ j y ≤ mInt A Ψ (fun _ => 1) := by
  have hKc : IsCompact ((A.chart j).symm '' K) :=
    hK.image_of_continuousOn ((A.chart j).continuousOn_symm.mono hKt)
  have hKs : (A.chart j).symm '' K ⊆ (A.chart j).source := by
    rintro _ ⟨y, hy, rfl⟩
    exact (A.chart j).map_target (hKt hy)
  obtain ⟨U, hU, hKU, hUs⟩ := normal_exists_closure_subset hKc.isClosed (A.chart j).open_source hKs
  obtain ⟨f, hf1, hf0, -, hf01⟩ := exists_continuous_one_zero_of_isCompact hKc hU.isClosed_compl
    (disjoint_compl_right.mono_left hKU)
  have hts : tsupport f ⊆ (A.chart j).source := by
    refine (closure_mono fun x hx => ?_).trans hUs
    by_contra h
    exact hx (hf0 h)
  have hint : MIntegrable A Ψ f := ReciprocityTheory.AnForm.M.mIntegrableCont A Ψ hΨ f f.continuous
  have hint' : MIntegrable A Ψ (fun x => 1 - f x) :=
    ReciprocityTheory.AnForm.M.mIntegrableCont A Ψ hΨ _ (continuous_const.sub f.continuous)
  have hne := ReciprocityTheory.AnForm.M.existsPartition A
  have hloc : mInt A Ψ f = ∫ y in (A.chart j).target, f ((A.chart j).symm y) * locDens A Ψ j y := by
    rw [ReciprocityTheory.AnForm.M.mIntEq A hne.some Ψ hΨ f hint]
    exact ReciprocityTheory.AnForm.M.mIntLocalize A hne.some Ψ hΨ j f hts hint
  have hT : IntegrableOn (fun y => f ((A.chart j).symm y) * locDens A Ψ j y) (A.chart j).target := by
    obtain ⟨hc, hsub⟩ := ReciprocityTheory.AnForm.M.image_closed_compact (A.chart j) (isClosed_tsupport f) hts
    refine ReciprocityTheory.AnForm.M.integrableOn_target_of_closed (A.chart j) (Z := tsupport f)
      (fun y _ hy => ?_) (hint j _ hsub hc)
    rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  have h1 : ∫ y in K, locDens A Ψ j y ≤ mInt A Ψ f := by
    rw [hloc]
    calc ∫ y in K, locDens A Ψ j y
        = ∫ y in K, f ((A.chart j).symm y) * locDens A Ψ j y := by
          refine setIntegral_congr_fun hK.measurableSet fun y hy => ?_
          simp [hf1 ⟨y, hy, rfl⟩]
      _ ≤ _ := by
          refine setIntegral_mono_set hT ?_ (Filter.Eventually.of_forall hKt)
          filter_upwards [ae_restrict_mem (A.chart j).open_target.measurableSet] with y hy
          exact mul_nonneg (hf01 _).1
            (ReciprocityTheory.AnForm.M.locDens_nonneg_of_psh A Ψ hΨ hpsh j hy)
  have h2 := ReciprocityTheory.AnForm.M.mIntLinear A Ψ hΨ 1 _ _ hint hint'
  have h3 : (fun x => 1 * f x + (1 - f x)) = fun _ : X => (1 : ℝ) := funext fun x => by ring
  rw [h3] at h2
  have h4 := ReciprocityTheory.AnForm.M.mIntNonneg A Ψ hΨ hpsh (fun x => 1 - f x)
    fun x => sub_nonneg.2 (hf01 x).2
  linarith

theorem integrable_of_tendsto_of_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {G : ℕ → α → ℝ} {F : α → ℝ} (hG : ∀ n, Integrable (G n) μ) (h0 : ∀ n, ∀ᵐ x ∂μ, 0 ≤ G n x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => G n x) atTop (𝓝 (F x))) (C : ℝ)
    (hC : ∀ n, ∫ x, G n x ∂μ ≤ C) : Integrable F μ := by
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hG n).1) hlim, ?_⟩
  have hF : ∫⁻ x, ‖F x‖ₑ ∂μ ≤ liminf (fun n => ∫⁻ x, ‖G n x‖ₑ ∂μ) atTop :=
    lintegral_congr_ae (by filter_upwards [hlim] with x hx using hx.enorm.liminf_eq) ▸
      lintegral_liminf_le' (fun n => (hG n).1.aemeasurable.enorm)
  have hb : ∀ n, ∫⁻ x, ‖G n x‖ₑ ∂μ ≤ ENNReal.ofReal C := by
    intro n
    have h1 : ∫⁻ x, ‖G n x‖ₑ ∂μ = ENNReal.ofReal (∫ x, G n x ∂μ) := by
      rw [ofReal_integral_eq_lintegral_ofReal (hG n) (h0 n)]
      refine lintegral_congr_ae ?_
      filter_upwards [h0 n] with x hx
      exact Real.enorm_eq_ofReal hx
    rw [h1]
    exact ENNReal.ofReal_le_ofReal (hC n)
  exact (hF.trans (liminf_le_of_frequently_le' (Frequently.of_forall hb))).trans_lt
    ENNReal.ofReal_lt_top

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot ChartPartition mInt integralWith locDens)

theorem tailLogBound_dim_zero {X : Type} [TopologicalSpace X] (A : FinHolAtlas 0 X) (Yo : Set X)
    (r : X → ℝ) (T : Fin 0 → LocPot X) : ∃ CE : ℝ, TailLogBound A Yo r T CE := by
  classical
  have hv : (volume : Measure (Fin 0 → ℂ)) Set.univ = 1 := by
    rw [volume_pi, Measure.pi_univ]
    simp
  have : IsFiniteMeasure (volume : Measure (Fin 0 → ℂ)) := ⟨by rw [hv]; exact ENNReal.one_lt_top⟩
  have hd : ∀ j y, locDens A T j y = 1 := fun j y => by
    simp [locDens, ReciprocityTheory.AnForm.maDens, ReciprocityTheory.AnForm.mdisc_zero]
  have hint : ∀ (f : (Fin 0 → ℂ) → ℝ) (K : Set (Fin 0 → ℂ)),
      ∫ y in K, f y = (volume K).toReal * f default := by
    intro f K
    have : f = fun _ => f default := funext fun y => congrArg f (Subsingleton.elim y default)
    rw [this, integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul]
  have hvol : ∀ K : Set (Fin 0 → ℂ), 0 ≤ (volume K).toReal ∧ (volume K).toReal ≤ 1 := fun K =>
    ⟨ENNReal.toReal_nonneg, by
      have := ENNReal.toReal_mono (by rw [hv]; exact ENNReal.one_ne_top)
        (measure_mono (μ := volume) (Set.subset_univ K))
      rwa [hv, ENNReal.toReal_one] at this⟩
  set p : Fin A.n → X := fun j => (A.chart j).symm default
  set B := ∑ j, |Real.log (r (p j))|
  set M := ∑ j, |r (p j)| + Real.exp 1
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hM : 0 < M := by positivity
  refine ⟨B * M, fun R₀ hR₀ => ⟨fun j K _ _ => Integrable.of_finite.integrableOn, ?_⟩⟩
  set g := (tail Yo r R₀).indicator fun x => Real.log (r x)
  have hR₀pos : 0 < R₀ := lt_of_lt_of_le (Real.exp_pos 1) hR₀
  have hlog : 1 ≤ Real.log R₀ := by
    have := Real.log_le_log (Real.exp_pos 1) hR₀
    rwa [Real.log_exp] at this
  have hg : ∀ x, |g x| ≤ |Real.log (r x)| := fun x => by
    simp only [g, Set.indicator]
    split_ifs <;> simp
  have hterm : ∀ (P : ChartPartition A) j,
      |∫ y in (A.chart j).target, P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) *
          locDens A T j y| ≤ |Real.log (r (p j))| ∧
        (M < R₀ → ∫ y in (A.chart j).target, P.χ j ((A.chart j).symm y) *
          g ((A.chart j).symm y) * locDens A T j y = 0) := by
    intro P j
    rw [hint, hd, mul_one]
    have hχ0 := P.nonneg j (p j)
    have hχ1 : P.χ j (p j) ≤ 1 := P.sum_eq_one (p j) ▸
      Finset.single_le_sum (fun i _ => P.nonneg i (p j)) (Finset.mem_univ j)
    obtain ⟨hv0, hv1⟩ := hvol (A.chart j).target
    refine ⟨?_, fun hMR => ?_⟩
    · rw [abs_mul, abs_mul, abs_of_nonneg hv0, abs_of_nonneg hχ0]
      have := hg (p j)
      have h2 : P.χ j (p j) * |g (p j)| ≤ |Real.log (r (p j))| := by nlinarith [abs_nonneg (g (p j))]
      nlinarith [abs_nonneg (g (p j))]
    · have hr : |r (p j)| ≤ ∑ i, |r (p i)| :=
        Finset.single_le_sum (f := fun i => |r (p i)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      have hn : p j ∉ tail Yo r R₀ := fun h => by
        have := h.2
        have := le_abs_self (r (p j))
        have := Real.exp_pos 1
        linarith
      show (volume (A.chart j).target).toReal * (P.χ j (p j) * g (p j)) = 0
      rw [show g (p j) = 0 from Set.indicator_of_notMem hn _]
      simp
  have hRHS : 0 ≤ B * M * Real.log R₀ ^ (0 + 1) / R₀ := by
    have : 0 ≤ Real.log R₀ := by linarith
    positivity
  show mInt A T g ≤ B * M * Real.log R₀ ^ (0 + 1) / R₀
  unfold mInt
  split_ifs with h
  · unfold integralWith
    by_cases hMR : M < R₀
    · rw [Finset.sum_eq_zero fun j _ => (hterm h.some j).2 hMR]
      exact hRHS
    · replace hMR := not_lt.mp hMR
      calc _ ≤ ∑ j, |Real.log (r (p j))| :=
            Finset.sum_le_sum fun j _ => (le_abs_self _).trans (hterm h.some j).1
        _ ≤ B * M * Real.log R₀ ^ (0 + 1) / R₀ := by
          rw [le_div_iff₀ hR₀pos, pow_one]
          have h1 : B * R₀ ≤ B * M := mul_le_mul_of_nonneg_left hMR hB
          have h2 : B * M ≤ B * M * Real.log R₀ := by
            have := mul_nonneg hB hM.le
            nlinarith
          linarith
  · exact hRHS

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection logNormSec)

noncomputable section

variable {D : ℕ} {X : Type*} [TopologicalSpace X]

def secOpen (s : X → X → ℂ) : Set X := {y | s y y ≠ 0}

def rSec (L : LocPot X) (s : X → X → ℂ) (y : X) : ℝ := Real.exp 1 - 2 * logNormSec L s y

structure IsLemmaEPot (A : FinHolAtlas D X) (Om : KaehlerForm A) (L : LocPot X)
    (s : X → X → ℂ) (C₁ : ℝ) (u : X → ℝ) : Prop where
  smooth : A.SmoothOn (secOpen s) u
  nonneg : FormNonneg A (secOpen s) (potForm Om.pot u)
  nonpos : ∀ x ∈ secOpen s, u x ≤ 0
  le_u : ∀ x ∈ secOpen s, -(C₁ * Real.log (rSec L s x)) ≤ u x
  smooth_or_pole : A.Smooth u ∨ ∀ y, y ∉ secOpen s → Tendsto u (𝓝[secOpen s] y) atBot

def LemmaETailLog.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (Om : KaehlerForm A) (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s →
    Dense (secOpen s) → (∀ y, ‖s y y‖ * Real.exp (-L.φ y y) ≤ 1) → ∀ C₁ : ℝ, 0 ≤ C₁ →
    ∃ CE : ℝ, ∀ u : Fin D → X → ℝ, (∀ i, IsLemmaEPot A Om L s C₁ (u i)) →
      TailLogBound A (secOpen s) (rSec L s) (fun i => potForm Om.pot (u i)) CE

section Inhabitants

open OnePoint
open ReciprocityTheory.AnForm.M (p1 fsPot projectiveLinePairSection projLine_isSmoothPotential projLine_isPlurisubharmonic projLine_isHolomorphicSection crd0 crd1 fsPot_φ_coe
  projLineSection_infty projLineSection_coe)

end Inhabitants

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential)

def BoundingKaehler.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (_ : KaehlerForm A) (m : ℕ) (th : Fin m → LocPot X), (∀ i, IsPotential A (th i)) →
    ∃ Om : KaehlerForm A, ∀ i,
      LeviLe A Set.univ 1 (th i) 1 Om.pot ∧ LeviLe A Set.univ (-1) Om.pot 1 (th i)

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end
