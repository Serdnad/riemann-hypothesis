module

public import ReciprocityTheory.L2DbarEstimates.Localization.LocalizeA
public import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle003
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ExistsChartPartition
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.TsupportDbSubset

@[expose] public section

section

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem localize (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hMD : MultDivStatement n M) (hMS : MultSStatement n M) :
    LocalizeStatement n M := by
  intro z hz H G D S hG hD hS hGD hGS hcG hcD hcS
  have := loc_weaklyLocallyCompact n z hz
  have hK : IsCompact (tsupport G ∪ tsupport D ∪ tsupport S) := (hcG.union hcD).union hcS
  set K := tsupport G ∪ tsupport D ∪ tsupport S with hKdef
  obtain ⟨K', hK', hKK'⟩ := exists_compact_superset hK
  obtain ⟨N, e, χ, he, hχs, hχc, hχsub, -, -, hχK⟩ :=
    exists_chart_partition n z hz K' univ hK' isOpen_univ (subset_univ _)
  have hck : ∀ i, Ck n z 1 (fun y => (χ i y : ℂ)) := fun i => SmoothR.ckR n z 1 (χ i) (hχs i)
  have hoff : ∀ x, x ∉ K → G x = 0 ∧ D x = 0 ∧ S x = 0 := fun x hx =>
    ⟨image_eq_zero_of_notMem_tsupport fun h => hx (Or.inl (Or.inl h)),
     image_eq_zero_of_notMem_tsupport fun h => hx (Or.inl (Or.inr h)),
     image_eq_zero_of_notMem_tsupport fun h => hx (Or.inr h)⟩
  have hone : ∀ x ∈ K, ∑ i, (χ i x : ℂ) = 1 := fun x hx => by
    rw [← Complex.ofReal_sum, hχK x (interior_subset (hKK' hx)), Complex.ofReal_one]
  have hev : ∀ x ∈ K, (fun y => ∑ i, (χ i y : ℂ)) =ᶠ[𝓝 x] fun _ => (1 : ℂ) := fun x hx => by
    filter_upwards [isOpen_interior.mem_nhds (hKK' hx)] with y hy
    rw [← Complex.ofReal_sum, hχK y (interior_subset hy), Complex.ofReal_one]
  have hdz : ∀ x ∈ K, ∀ j, ∑ i, d n z j (fun y => (χ i y : ℂ)) x = 0 := fun x hx j => by
    rw [← loc_d_sum n z Finset.univ _ hck j x, loc_d_congr n z hz j _ _ x (hev x hx), d_const]
  have hdbz : ∀ x ∈ K, ∀ j, ∑ i, db n z j (fun y => (χ i y : ℂ)) x = 0 := fun x hx j => by
    rw [← loc_db_sum n z Finset.univ _ hck j x, loc_db_congr n z hz j _ _ x (hev x hx), db_const]
  have sG : ∀ x, G x = ∑ i, locG (χ i) G x := fun x => by
    by_cases hx : x ∈ K
    · simp only [locG]; rw [← Finset.sum_smul, hone x hx, one_smul]
    · simp [locG, (hoff x hx).1]
  have sD : ∀ x, D x = ∑ i, locD n z (χ i) G D x := fun x => by
    by_cases hx : x ∈ K
    · simp only [locD, Finset.sum_add_distrib, ← Finset.sum_mul, hone x hx, one_mul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, hdz x hx, zero_mul, Finset.sum_const_zero, add_zero]
    · simp [locD, (hoff x hx).1, (hoff x hx).2.1]
  have sS : ∀ x j k, S x j k = ∑ i, locS n z (χ i) G S x j k := fun x j k => by
    by_cases hx : x ∈ K
    · simp only [locS, wedge, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
        hone x hx, one_mul, hdbz x hx, zero_mul, sub_self, add_zero]
    · simp [locS, wedge, (hoff x hx).1, (hoff x hx).2.2]
  have hP := fun i => loc_piece n z hz hMD hMS (χ i) (hχs i) (hχc i) (e i).source
    ((hχsub i).trans inter_subset_left) G D S hG hD hS hGD hGS
  choose K0 hK0 happ using fun i => H (e i) _ _ _ (he i) (hP i).1 (hP i).2.1 (hP i).2.2.1
    (hP i).2.2.2.1 (hP i).2.2.2.2.1 (hP i).2.2.2.2.2.1 (hP i).2.2.2.2.2.2.1
    (hP i).2.2.2.2.2.2.2.1 (hP i).2.2.2.2.2.2.2.2.1 (hP i).2.2.2.2.2.2.2.2.2.1
    (hP i).2.2.2.2.2.2.2.2.2.2
  refine ⟨⋃ i, K0 i, isCompact_iUnion hK0, fun δ hδ => ?_⟩
  obtain ⟨δ', hδ'0, hδ'⟩ := ENNReal.exists_pos_mul_lt (a := (N : ℝ≥0∞) * N) (b := δ)
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) (ENNReal.natCast_ne_top N)) hδ.ne'
  choose g hgT hg0 hg1 hg2 hg3 using fun i => happ i δ' hδ'0
  have hgc : ∀ i j, Ck n z 2 (fun x => g i x j) := fun i j => (hgT i j).1
  have hgc1 : ∀ i j, Ck n z (0 + 1) (fun x => g i x j) := fun i j =>
    Ck.mono n z 1 2 (by norm_num) _ (hgc i j)
  have hfun : ∀ j, (fun x => (∑ i, g i x) j) = fun x => ∑ i, g i x j := fun j =>
    funext fun x => loc_sum_apply _ j
  have hvan : ∀ x, x ∉ ⋃ i, K0 i → ∑ i, g i x = 0 := fun x hx =>
    Finset.sum_eq_zero fun i _ => hg0 i x fun h => hx (mem_iUnion.2 ⟨i, h⟩)
  have hgcont : ∀ i, Continuous (g i) := fun i => by
    have : Continuous (fun x => WithLp.toLp 2 (fun j => g i x j)) :=
      (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => Ck.continuous n z hz 2 _ (hgc i j))
    exact this
  have hdivc : ∀ i, Continuous (divF n z (g i)) := fun i => by
    unfold divF
    exact continuous_finsetSum _ fun j _ => Ck.continuous n z hz 0 _ (Ck.d n z 0 j _ (hgc1 i j))
  have hsbc : ∀ i, Continuous (sbar n z (g i)) := fun i => by
    unfold sbar
    exact continuous_pi fun j => continuous_pi fun k =>
      (Ck.continuous n z hz 0 _ (Ck.db n z 0 j _ (hgc1 i k))).sub
        (Ck.continuous n z hz 0 _ (Ck.db n z 0 k _ (hgc1 i j)))
  have hdiv : ∀ x, divF n z (fun x => ∑ i, g i x) x = ∑ i, divF n z (g i) x := fun x => by
    simp only [divF]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hfun j, loc_d_sum n z Finset.univ (fun i y => g i y j) (fun i => hgc1 i j) j x]
  have hsb : ∀ x j k, sbar n z (fun x => ∑ i, g i x) x j k = ∑ i, sbar n z (g i) x j k :=
    fun x j k => by
    simp only [sbar]
    rw [hfun k, hfun j, loc_db_sum n z _ (fun i y => g i y k) (fun i => hgc1 i k) j x,
      loc_db_sum n z _ (fun i y => g i y j) (fun i => hgc1 i j) k x, Finset.sum_sub_distrib]
  refine ⟨fun x => ∑ i, g i x, fun j => ⟨?_, ?_⟩, hvan, ?_, ?_, ?_⟩
  · rw [hfun j]; exact loc_ck_sum n z 2 _ _ fun i => hgc i j
  · refine HasCompactSupport.intro (isCompact_iUnion hK0) fun x hx => ?_
    show (∑ i, g i x) j = 0
    rw [hvan x hx]; rfl
  · unfold nV
    refine loc_lintegral_sum_lt (vol n z) _ (fun i x => ENNReal.ofReal (‖g i x - locG (χ i) G x‖ ^ 2 *
      Real.exp (-(fun _ : M => (0 : ℝ)) x))) (fun i => loc_aem _ _ ((hgcont i).aestronglyMeasurable.sub
      (hP i).1.1)) (fun x => ?_) δ' δ (fun i => hg1 i) hδ'
    simp only [neg_zero, Real.exp_zero, mul_one]
    have : (∑ i, g i x) - G x = ∑ i, (g i x - locG (χ i) G x) := by
      rw [Finset.sum_sub_distrib, ← sG x]
    rw [this]
    exact loc_ofReal_le _ (fun i => by positivity) _ (loc_norm_sum_sq _)
  · unfold wint
    refine loc_lintegral_sum_lt (vol n z) _ (fun i x => ENNReal.ofReal
      (‖divF n z (g i) x - locD n z (χ i) G D x‖ ^ 2 * Real.exp (-(fun _ : M => (0 : ℝ)) x)))
      (fun i => loc_aem _ _ ((hdivc i).aestronglyMeasurable.sub (hP i).2.1.1)) (fun x => ?_) δ' δ
      (fun i => hg2 i) hδ'
    simp only [neg_zero, Real.exp_zero, mul_one]
    have : divF n z (fun x => ∑ i, g i x) x - D x =
        ∑ i, (divF n z (g i) x - locD n z (χ i) G D x) := by
      rw [hdiv x, Finset.sum_sub_distrib, ← sD x]
    rw [this]
    exact loc_ofReal_le _ (fun i => by positivity) _ (loc_norm_sum_sq _)
  · unfold n2
    refine loc_lintegral_sum_lt (vol n z) _ (fun i x => ENNReal.ofReal
      (sq2 n (sbar n z (g i) x - locS n z (χ i) G S x) * Real.exp (-(fun _ : M => (0 : ℝ)) x)))
      (fun i => aemeasurable_unweighted_two_form _ _ ((hsbc i).aestronglyMeasurable.sub (hP i).2.2.1.1)) (fun x => ?_) δ' δ
      (fun i => hg3 i) hδ'
    simp only [neg_zero, Real.exp_zero, mul_one]
    have : sbar n z (fun x => ∑ i, g i x) x - S x =
        fun j k => ∑ i, (sbar n z (g i) x - locS n z (χ i) G S x) j k := by
      funext j k
      simp only [Pi.sub_apply]
      rw [hsb x j k, sS x j k, Finset.sum_sub_distrib]
    rw [this]
    exact loc_ofReal_le _ (fun i => two_form_norm_sq_nonneg _ _) _ (two_form_sq_finset_sum_le _)

end

end ReciprocityTheory.L2DbarEstimates.F
end

section

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem ti_le_of_forall_pos (x c Y : ℝ≥0∞)
    (h : ∀ ε : ℝ, 0 < ε → x ≤ c * (ENNReal.ofReal (1 + ε) * Y)) : x ≤ c * Y := by
  have hc : Continuous fun ε : ℝ => ENNReal.ofReal (1 + ε) :=
    ENNReal.continuous_ofReal.comp (continuous_const.add continuous_id)
  have ht0 : Tendsto (fun ε : ℝ => ENNReal.ofReal (1 + ε)) (𝓝[>] 0) (𝓝 1) := by
    have h1 := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using h1
  have ht : Tendsto (fun ε : ℝ => ENNReal.ofReal (1 + ε) * (c * Y)) (𝓝[>] 0) (𝓝 (c * Y)) := by
    have h1 := ENNReal.Tendsto.mul_const (b := c * Y) ht0 (Or.inl one_ne_zero)
    simpa using h1
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => by
    calc x ≤ c * (ENNReal.ofReal (1 + ε) * Y) := h ε hε
      _ = ENNReal.ofReal (1 + ε) * (c * Y) := by ring)

theorem ti_hasCompactSupport {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (f : M → V n) (hf : IsTestForm n z f) : HasCompactSupport f := by
  have h : ∀ j, HasCompactSupport (fun x => f x j) := fun j => (hf j).2
  have hsub : Function.support f ⊆ ⋃ j, Function.support (fun x => f x j) := by
    intro x hx
    rw [Set.mem_iUnion]
    by_contra hne
    push_neg at hne
    apply hx
    ext j
    simpa [Function.mem_support] using hne j
  have hts : tsupport f ⊆ ⋃ j, tsupport (fun x => f x j) := by
    show closure (Function.support f) ⊆ ⋃ j, closure (Function.support fun x => f x j)
    rw [← closure_iUnion_of_finite]
    exact closure_mono hsub
  exact IsCompact.of_isClosed_subset (isCompact_iUnion fun j => h j) (isClosed_tsupport f) hts

private theorem db_eq_wdb_comp_symm_of_isChart {M : Type*} [TopologicalSpace M] {n : ℕ} {z : M → V n}
    (j : Fin n) (f : M → ℂ) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) {x : M}
    (hx : x ∈ e.source) : db n z j f x = wdb n j (f ∘ e.symm) (z x) := by
  have hex : ∃ c : OpenPartialHomeomorph M (V n), IsChart n z c ∧ x ∈ c.source := ⟨e, he, hx⟩
  rw [db, dite_eq_left hex]
  obtain ⟨hc, hxc⟩ := Classical.choose_spec hex
  apply wdb_congr
  have hzx : z x = e x := he hx
  have hzc : z x = (Classical.choose hex) x := hc hxc
  have h1 : ∀ᶠ y in 𝓝 (z x), y ∈ e.target := by
    rw [hzx]
    exact e.open_target.mem_nhds (e.map_source hx)
  have h2 : ∀ᶠ y in 𝓝 (z x), y ∈ (Classical.choose hex).target := by
    rw [hzc]
    exact (Classical.choose hex).open_target.mem_nhds ((Classical.choose hex).map_source hxc)
  have h3 : ∀ᶠ y in 𝓝 (z x), e.symm y ∈ (Classical.choose hex).source := by
    have hca : ContinuousAt e.symm (z x) := by
      rw [hzx]
      exact e.continuousAt_symm (e.map_source hx)
    apply hca.preimage_mem_nhds
    rw [hzx, e.left_inv hx]
    exact (Classical.choose hex).open_source.mem_nhds hxc
  filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
  show f ((Classical.choose hex).symm y) = f (e.symm y)
  congr 1
  apply (Classical.choose hex).injOn ((Classical.choose hex).map_target hy2) hy3
  rw [(Classical.choose hex).right_inv hy2, ← hc hy3, he (e.map_target hy1), e.right_inv hy1]

private theorem ck_one_db_of_smooth {M : Type*} [TopologicalSpace M] {n : ℕ} {z : M → V n} {F : M → ℂ}
    (hF : Smooth n z F) (j : Fin n) : Ck n z 1 (fun x => db n z j F x) := by
  intro e he
  have hG : ContDiffOn ℝ 2 (F ∘ e.symm) e.target := (hF e he).of_le (by first
      | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤)
      | exact WithTop.coe_le_coe.mpr le_top
      | simp)
  have hD : ContDiffOn ℝ 1 (fun y => fderiv ℝ (F ∘ e.symm) y) e.target :=
    hG.fderiv_of_isOpen e.open_target (by norm_num)
  have hW : ContDiffOn ℝ 1 (fun y => wdb n j (F ∘ e.symm) y) e.target := by
    unfold wdb
    exact ((hD.clm_apply contDiffOn_const).add
      (contDiffOn_const.mul (hD.clm_apply contDiffOn_const))).div_const _
  refine hW.congr fun y hy => ?_
  show db n z j F (e.symm y) = wdb n j (F ∘ e.symm) y
  rw [db_eq_wdb_comp_symm_of_isChart j F e he (e.map_target hy), he (e.map_target hy), e.right_inv hy]

private theorem smoothR_sub_const_mul {M : Type*} [TopologicalSpace M] {n : ℕ} {z : M → V n}
    {a b : M → ℝ} (ha : SmoothR n z a) (hb : SmoothR n z b) (c : ℝ) :
    SmoothR n z (fun x => a x - c * b x) := by
  intro e he
  refine ((ha e he).sub ((contDiffOn_const (c := ((c : ℝ) : ℂ))).mul (hb e he))).congr
    fun y _ => ?_
  simp [Function.comp]

theorem testIneq (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hCh : ChoiceStatement n M) (hP : PrimedIneqStatement n M)
    (hC : ClosureIneqStatement n M) (hS : SplitTestStatement n M) (hL : LocalityStatement n M)
    (hWS : WeakSSmoothStatement n M) (hSD : SbarDbarStatement n M) : TestIneqStatement n M := by
  intro X ph F0 h hph hlev hF0 hh hdom hI f hf
  have hz := X.isLocalHomeomorph
  apply ti_le_of_forall_pos
  intro ε hε
  have hck2 : Ck n X.z 2 F0 := fun e he => (hF0 e he).of_le (by first
      | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤)
      | exact WithTop.coe_le_coe.mpr le_top
      | simp)
  have hcj : ∀ j, Continuous fun x => db n X.z j F0 x := by
    intro j
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨e, hxe, hze⟩ := hz x
    have he : IsChart n X.z e := fun y _ => by rw [hze]
    have hC := (ck_one_db_of_smooth hF0 j e he).continuousOn
    have h1 : ContinuousOn (((fun x => db n X.z j F0 x) ∘ e.symm) ∘ e) e.source :=
      hC.comp e.continuousOn (fun y hy => e.map_source hy)
    have h2 : ContinuousOn (fun x => db n X.z j F0 x) e.source :=
      h1.congr fun y hy => by simp [e.left_inv hy]
    exact h2.continuousAt (e.open_source.mem_nhds hxe)
  have hcont : Continuous (dbarF n X.z F0) := by
    show Continuous fun x => WithLp.toLp 2 (fun j => db n X.z j F0 x)
    first
      | exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp (continuous_pi hcj)
      | exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin n => ℂ)).comp (continuous_pi hcj)
      | fun_prop
  obtain ⟨ph', ψ, e', U, hph', hψ, he', hcut, hU, hCU, hUeq, hle, hlevi, hL2⟩ :=
    hCh X ph (dbarF n X.z F0) (tsupport f) ε hph hcont (ti_hasCompactSupport n X.z f hf) hε
  have hprim := hP X.z hz ph ph' ψ F0 h ε hph hlev hph' hψ hF0 hh hdom hε hle hlevi hI
  have hclos := hC X.z hz e' ph' ψ (dbarF n X.z F0) _ ε he' hph' hψ hcut hL2 hI hε hprim
  have hw1 : SmoothR n X.z (w1 ph' ψ) := smoothR_sub_const_mul hph' hψ 2
  have hw2 : SmoothR n X.z (w2 ph' ψ) := by
    have h1 := smoothR_sub_const_mul hph' hψ 1
    simp only [one_mul] at h1
    exact h1
  have hWS0 : IsWeakS n X.z (dbarF n X.z F0) 0 := by
    have h1 := hWS X.z hz (dbarF n X.z F0) (fun j => ck_one_db_of_smooth hF0 j)
    have h0 : sbar n X.z (dbarF n X.z F0) = 0 := by
      funext x
      exact hSD X.z hz F0 hck2 x
    rwa [h0] at h1
  obtain ⟨hT, f₁, hf₁, hS1, hadj, hip⟩ :=
    hS X.z hz (w1 ph' ψ) (w2 ph' ψ) (dbarF n X.z F0) f hw1 hw2 hL2 hWS0 hf
  obtain ⟨hloc1, hloc2⟩ := hL X.z hz ph ph' ψ U f hU hf hCU hUeq
  have hfin := hclos f₁ (tstar n X.z (w1 ph' ψ) (w2 ph' ψ) f) hf₁ hT hadj hS1
  rw [← hip, hloc1, hloc2] at hfin
  exact hfin

end

end ReciprocityTheory.L2DbarEstimates.F
end
