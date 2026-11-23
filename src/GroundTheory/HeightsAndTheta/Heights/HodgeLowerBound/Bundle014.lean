module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle012
import Aesop.Main
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogIntPoly
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Counterexample.Objects
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightObjects
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle024
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightPtsIntegralPoints
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.Bundle001

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Set
open ReciprocityTheory.AnForm.A (coordDiv)

theorem volume_coordDiv {D : ℕ} (S : Finset (Fin D)) : volume (coordDiv S) = 0 := by
  have h : coordDiv S = ⋃ i ∈ S, (fun z : Fin D → ℂ => z i) ⁻¹' {0} := by
    ext z
    simp [coordDiv]
  rw [h]
  exact measure_iUnion_null fun i => measure_iUnion_null fun _ =>
    Measure.pi_eval_preimage_null (fun _ : Fin D => (volume : Measure ℂ)) (measure_singleton 0)

theorem DivisorPreimageNull.proof (h : ParamImageNull.Statement) : DivisorPreimageNull.Statement := by
  intro K _ ι _ P d M R
  classical
  have hloc : ∀ x : M.Xc, ∃ W : Set M.Xc, IsOpen W ∧ x ∈ W ∧ ∃ j : Fin R.N, W ⊆ (R.chart j).source ∧
      ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y ∈ W, s y ∈ mcPts P ∧ M.proj (s y) = y) ∧
        ∀ p, M.atlas.HoloOn W fun y => s y p := by
    intro x
    obtain ⟨U, hU, hxU, s, hs, hhol⟩ := M.sections x
    obtain ⟨j, hj⟩ := R.cover x
    refine ⟨U ∩ (R.chart j).source, hU.inter (R.chart j).open_source,
      ⟨hxU, R.mid_subset_source j (R.inner_subset_mid j hj)⟩, j, inter_subset_right, s,
      fun y hy => hs y hy.1, fun p i => ?_⟩
    exact (hhol p i).mono (inter_subset_inter_right _ (preimage_mono inter_subset_left))
  choose W hWo hxW j hWj s hs hhol using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hWo (fun x _ => mem_iUnion.2 ⟨x, hxW x⟩)
  let xs : Fin t.card → M.Xc := fun i => (t.equivFin.symm i : M.Xc)
  refine h K ι P d t.card (fun i => R.chart (j (xs i)) '' W (xs i))
    (fun i => R.chart (j (xs i)) '' W (xs i) ∩ coordDiv (R.S (j (xs i))))
    (fun i w => s (xs i) ((R.chart (j (xs i))).symm w)) {z | M.proj z ∉ R.Yo}
    (fun i => (R.chart (j (xs i))).isOpen_image_of_subset_source (hWo _) (hWj _))
    (fun i => inter_subset_left)
    (fun i => measure_mono_null inter_subset_right (volume_coordDiv _)) ?_ ?_
  · rintro i w ⟨y, hyW, rfl⟩
    refine analyticAt_pi_iff.2 fun p => ?_
    exact GroundTheory.Heights₂.Heights.Regular.analyticAt_comp_symm_of_holoOn (R.compat _) (hhol (xs i) p) hyW
      (hWj _ hyW)
  · rintro z ⟨hzY, hz⟩
    obtain ⟨x, hxt, hzW⟩ := mem_iUnion₂.1 (ht (mem_univ (M.proj z)))
    obtain ⟨i, rfl⟩ : ∃ i, xs i = x := ⟨t.equivFin ⟨x, hxt⟩, by simp [xs]⟩
    have hsrc := hWj (xs i) hzW
    have hdiv : R.chart (j (xs i)) (M.proj z) ∈ coordDiv (R.S (j (xs i))) := by
      by_contra hc
      exact hzY ((R.mem_Yo _ _ hsrc).2 hc)
    refine ⟨i, R.chart (j (xs i)) (M.proj z), ⟨⟨M.proj z, hzW, rfl⟩, hdiv⟩, ?_⟩
    have hγ : s (xs i) ((R.chart (j (xs i))).symm (R.chart (j (xs i)) (M.proj z))) = s (xs i) (M.proj z) := by
      rw [(R.chart (j (xs i))).left_inv hsrc]
    rw [hγ]
    obtain ⟨hsm, hsp⟩ := hs (xs i) (M.proj z) hzW
    exact (M.fibre _ hsm z hz).1 hsp

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm.A (coordDiv)

namespace ModelLogIntegrableAlt

theorem volume_coordDiv {D : ℕ} (S : Finset (Fin D)) : volume (coordDiv S) = 0 := by
  have h : coordDiv S = ⋃ i ∈ S, (fun z : Fin D → ℂ => z i) ⁻¹' {0} := by
    ext z
    simp [coordDiv]
  rw [h]
  refine (measure_biUnion_null_iff S.countable_toSet).2 fun i _ => ?_
  rw [volume_pi]
  exact Measure.pi_eval_preimage_null _ (measure_singleton 0)

theorem target_inter_compl_Yo_subset {D : ℕ} {X : Type*} [TopologicalSpace X]
    {A : ReciprocityTheory.AnForm.M.FinHolAtlas D X} (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A) (j : Fin R.N) :
    (R.chart j).target ∩ (R.chart j).symm ⁻¹' R.Yoᶜ ⊆ coordDiv (R.S j) := by
  rintro y ⟨hy, hyY⟩
  have h := R.mem_Yo j _ ((R.chart j).map_target hy)
  rw [(R.chart j).right_inv hy] at h
  by_contra hc
  exact hyY (h.2 hc)

end ModelLogIntegrableAlt


open ModelLogIntegrableAlt in
theorem ModelLogIntegrable.proof (hM : ModelPtsIntegrable.Statement) : ModelLogIntegrable.Statement := by
  intro K _ ι _ P e M R L c N u C C' g hP hL hN hu hbd hg
  let _ : MeasurableSpace M.Xc := borel M.Xc
  have _ : BorelSpace M.Xc := ⟨rfl⟩
  obtain ⟨B, hB⟩ := R.f_bdd
  refine hM K ι P e M R.N R.chart L c N R.Yoᶜ u g hP hL hN R.compat (fun x => ?_)
    (fun j => measure_mono_null (target_inter_compl_Yo_subset R j) (volume_coordDiv _))
    (fun j Q hQ hQc => ?_) (fun z hz hzN hzE => hg z hz hzN (not_not.mp hzE))
  · obtain ⟨j, hj⟩ := R.cover x
    exact ⟨j, R.toPotentialCharts.mid_subset_source j (R.toPotentialCharts.inner_subset_mid j hj)⟩

  have hQp : Q ⊆ GroundTheory.Heights₂.Heights.LogInt.polydisc (Fin e) 1 := by
    intro y hy
    have hb : ‖y‖ < 1 := by simpa using R.target_subset j (hQ hy)
    intro i _
    simpa using (norm_le_pi_norm y i).trans hb.le
  set G : (Fin e → ℂ) → ℝ := fun y => |C| + |C'| * (Real.exp 1 + B) +
    |C'| * ∑ i ∈ R.S j, 2 * |Real.log ‖y i‖| with hGdef
  have hG : IntegrableOn G Q := by
    refine IntegrableOn.mono_set ?_ hQp
    refine ((integrableOn_const (GroundTheory.Heights₂.Heights.LogInt.volume_polydisc_ne_top 1)).add
      (Integrable.const_mul (integrable_finsetSum _ fun i _ =>
        ((GroundTheory.Heights₂.Heights.LogInt.integrableOn_log_norm_coord 1 i).abs.const_mul 2)) _))
  have hmeas : AEStronglyMeasurable (fun y => u ((R.chart j).symm y)) (volume.restrict Q) :=
    (hu.comp_aemeasurable (((R.chart j).continuousOn_symm.mono hQ).aemeasurable
      hQc.isClosed.measurableSet)).aestronglyMeasurable
  refine Integrable.mono' hG hmeas ?_
  filter_upwards [ae_restrict_mem hQc.isClosed.measurableSet,
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp (volume_coordDiv (R.S j)))] with y hyQ hyD
  have hyt := hQ hyQ
  have hYo : (R.chart j).symm y ∈ R.Yo := by
    have h := R.mem_Yo j _ ((R.chart j).map_target hyt)
    rw [(R.chart j).right_inv hyt] at h
    exact h.2 hyD
  have h1 := hbd _ hYo
  have hr1 := R.one_le_r _ hYo
  have hrc := R.r_chart j y ⟨hyt, hyD⟩
  set r := R.r ((R.chart j).symm y) with hrdef
  have hlog0 : 0 ≤ Real.log r := Real.log_nonneg hr1
  have hlogr : Real.log r ≤ r := by linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < r)]
  have hf : R.f j y ≤ B := (le_abs_self _).trans (hB j y hyt)
  have hsum : ∑ i ∈ R.S j, Real.log (‖y i‖ ^ 2)⁻¹ ≤ ∑ i ∈ R.S j, 2 * |Real.log ‖y i‖| := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Real.log_inv, Real.log_pow]
    push_cast
    linarith [neg_abs_le (Real.log ‖y i‖)]
  have hrb : r ≤ Real.exp 1 + B + ∑ i ∈ R.S j, 2 * |Real.log ‖y i‖| := by
    rw [hrc]; linarith
  have hC : C + C' * Real.log r ≤ |C| + |C'| * r := by
    have := mul_le_mul_of_nonneg_right (le_abs_self C') hlog0
    have := mul_le_mul_of_nonneg_left hlogr (abs_nonneg C')
    linarith [le_abs_self C]
  have hC2 : |C'| * r ≤ |C'| * (Real.exp 1 + B) + |C'| * ∑ i ∈ R.S j, 2 * |Real.log ‖y i‖| := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C')
  rw [Real.norm_eq_abs, hGdef]
  linarith

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace FsInvPow

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem fsHerm_h_eq (a : K → ℤ) (z : (Σ k, ι k) → ℂ) :
    (fsHerm ι a).h z = (HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) a).h z := by
  rw [fsHerm_h, Inter.ofMetrics_fs_h]
  unfold refNorm
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← sq_rpow_half (Real.sqrt_nonneg _) (a k),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

theorem isSmoothHerm_fsHerm (a : K → ℤ) : IsSmoothHerm (fsHerm ι a) := by
  have h : (fsHerm ι a).h = (HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) a).h :=
    funext (fsHerm_h_eq a)
  unfold IsSmoothHerm
  rw [h]
  exact Inter.isSmoothHerm_ofMetrics_fs a

theorem isSmoothHerm_fsMulti : IsSmoothHerm (GroundTheory.Heights₂.Heights.fsMulti ι) := by
  unfold GroundTheory.Heights₂.Heights.fsMulti
  exact Inter.isSmoothHerm_ofMetrics_fs _

abbrev invTensor (ι : K → Type) [∀ k, Fintype (ι k)] : _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι :=
  (fsHerm ι (fun _ => -1)).tensor (GroundTheory.Heights₂.Heights.fsMulti ι)

theorem isSmoothHerm_invTensor : IsSmoothHerm (invTensor ι) := by
  show ContDiffOn ℝ _ (fun z => (fsHerm ι (fun _ => -1)).h z * (GroundTheory.Heights₂.Heights.fsMulti ι).h z) _
  exact (isSmoothHerm_fsHerm _).mul isSmoothHerm_fsMulti

theorem invTensor_a (k : K) : (invTensor ι).a k = ((0 : K → ℕ) k : ℤ) := by
  show (-1 : ℤ) + 1 = _
  simp

theorem invTensor_h {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : (invTensor ι).h z = 1 := by
  show (fsHerm ι (fun _ => -1)).h z * (GroundTheory.Heights₂.Heights.fsMulti ι).h z = 1
  rw [fsHerm_h_eq]
  unfold GroundTheory.Heights₂.Heights.fsMulti
  rw [Inter.ofMetrics_fs_h, Inter.ofMetrics_fs_h, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun k _ => ?_
  obtain ⟨i, hi⟩ := hz k
  have hS : Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 (Finset.sum_pos' (fun j _ => sq_nonneg ‖z ⟨k, j⟩‖)
      ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩)).ne'
  show Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ (-1 : ℤ) * Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ (1 : ℤ) = 1
  rw [zpow_neg_one, zpow_one]
  exact inv_mul_cancel₀ hS


omit [∀ k, Fintype (ι k)] in
theorem ptsIntegral_eq_zero {e : ℕ} (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (g : ((Σ k, ι k) → ℂ) → ℝ) (hg : ∀ z ∈ mcPts P, g z = 0) : ptsIntegral P φ g = 0 := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    have h0 : ∀ y w, sheetDensity P hΨ.choose φ g y w = 0 := by
      intro y w
      unfold sheetDensity
      split_ifs with hγ
      · rw [hg _ hγ.choose_spec.2.self_of_nhds.2.1, zero_mul]
      · rfl
    simp [h0]
  · rfl

theorem snoc_invTensor (II : IntersectionSystem) (hII : IsIntersectionSystem II) (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hP : IsArithVar P (n + 1)) (hL : ∀ j, IsSmoothHerm (L j)) :
    II K ι P (n + 1) (Fin.snoc L (invTensor ι)) = 0 := by
  have h1 : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (1 : MRing ι) (0 : K → ℕ) := by
    classical
    intro m hm k
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
    split_ifs at hm with h
    · subst h
      simp
    · exact absurd rfl hm
  have hne : (1 : MRing ι) ∉ P := fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)
  rw [(hII K ι).2.2 P n L (invTensor ι) 1 0 hP hL isSmoothHerm_invTensor invTensor_a h1 hne]
  unfold recR
  have hsupp : divSupp P (1 : MRing ι) = ∅ := by
    unfold divSupp
    rw [Ideal.span_singleton_one, sup_top_eq, Ideal.minimalPrimes_top]
    simp
  have hint : arInt P 1 (invTensor ι) L = 0 := by
    unfold arInt
    refine ptsIntegral_eq_zero P _ _ fun z hz => ?_
    simp [logNorm, invTensor_h hz.1]
  simp [hsupp, hint]

theorem intersection_update_fsHerm_neg_one (II : IntersectionSystem) (hII : IsIntersectionSystem II) (P : Ideal (MRing ι)) (n : ℕ)
    (M : Fin (n + 1) → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hP : IsArithVar P (n + 1)) (hM : ∀ i, IsSmoothHerm (M i))
    (j : Fin (n + 1)) :
    II K ι P (n + 1) (Function.update M j (fsHerm ι fun _ => -1)) =
      -II K ι P (n + 1) (Function.update M j (GroundTheory.Heights₂.Heights.fsMulti ι)) := by
  let σ := Equiv.swap j (Fin.last n)
  let L : Fin n → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun i => M (σ (Fin.castSucc i))
  have hL : ∀ i, IsSmoothHerm (L i) := fun i => hM _
  have key : ∀ C, Function.update M j C ∘ σ = Fin.snoc L C := by
    intro C
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [σ]
    · simp only [Function.comp_apply, Fin.snoc_castSucc, L]
      rw [Function.update_of_ne]
      intro h
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h
      exact (Fin.castSucc_lt_last i).ne h
  have hsm : ∀ C, IsSmoothHerm C → ∀ i, IsSmoothHerm (Function.update M j C i) := by
    intro C hC i
    by_cases h : i = j
    · subst h
      simpa using hC
    · rw [Function.update_of_ne h]
      exact hM i
  have hsym : ∀ C, IsSmoothHerm C →
      II K ι P (n + 1) (Function.update M j C) = II K ι P (n + 1) (Fin.snoc L C) := by
    intro C hC
    rw [← key C]
    exact ((hII K ι).1 P (n + 1) _ σ hP (hsm C hC)).symm
  rw [hsym _ (isSmoothHerm_fsHerm _), hsym _ isSmoothHerm_fsMulti]
  have hadd := (hII K ι).2.1 P n L (fsHerm ι fun _ => -1) (GroundTheory.Heights₂.Heights.fsMulti ι) hP hL
    (isSmoothHerm_fsHerm _) isSmoothHerm_fsMulti
  rw [snoc_invTensor II hII P n L hP hL] at hadd
  linarith

theorem proof : FsInvPow.Statement := by
  intro II K _ ι _ P d hII hP
  cases d with
  | zero =>
    rw [pow_zero, one_mul]
    congr 1
    funext i
    exact i.elim0
  | succ n =>
    let M : ℕ → Fin (n + 1) → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun k i =>
      if (i : ℕ) < k then GroundTheory.Heights₂.Heights.fsMulti ι else fsHerm ι fun _ => -1
    have hM : ∀ k i, IsSmoothHerm (M k i) := by
      intro k i
      dsimp only [M]
      split_ifs
      · exact isSmoothHerm_fsMulti
      · exact isSmoothHerm_fsHerm _
    have step : ∀ k, (hk : k < n + 1) →
        II K ι P (n + 1) (M k) = -II K ι P (n + 1) (M (k + 1)) := by
      intro k hk
      have h1 : Function.update (M k) ⟨k, hk⟩ (fsHerm ι fun _ => -1) = M k := by
        funext i
        by_cases h : i = ⟨k, hk⟩
        · subst h
          simp [M]
        · rw [Function.update_of_ne h]
      have h2 : Function.update (M k) ⟨k, hk⟩ (GroundTheory.Heights₂.Heights.fsMulti ι) = M (k + 1) := by
        funext i
        by_cases h : i = ⟨k, hk⟩
        · subst h
          simp [M]
        · rw [Function.update_of_ne h]
          have hik : (i : ℕ) ≠ k := fun e => h (Fin.ext e)
          dsimp only [M]
          by_cases hi : (i : ℕ) < k
          · rw [if_pos hi, if_pos (by omega)]
          · rw [if_neg hi, if_neg (by omega)]
      rw [← h1, ← h2]
      exact intersection_update_fsHerm_neg_one II hII P n (M k) hP (hM k) ⟨k, hk⟩
    have hpow : ∀ k, k ≤ n + 1 → II K ι P (n + 1) (M 0) = (-1) ^ k * II K ι P (n + 1) (M k) := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        rw [ih (by omega), step k (by omega), pow_succ]
        ring
    have h0 : M 0 = fun _ => fsHerm ι fun _ => -1 := by
      funext i
      simp [M]
    have hd : M (n + 1) = fun _ => GroundTheory.Heights₂.Heights.fsMulti ι := by
      funext i
      simp [M, i.isLt]
    rw [← h0, ← hd]
    exact hpow (n + 1) le_rfl

end FsInvPow

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo Line

section Curve

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem inter_constLine_eq [Nonempty K] (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → Geo.HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) {W : Ideal (MRing ι)} (hW : IsArithVar W 1)
    (hH : IsMultiHomogIdeal W) (hdeg : 0 < degC W) (M : ℝ) (hM : 0 < M) :
    I W 1 ![constLine M hM] = Real.log M * degC W := by
  obtain ⟨c, hc⟩ := exists_chartMon_notMem hW
  rw [inter_eq_recR I hI hW (isSmoothHerm_constLine M hM) (d := 0) (fun k ↦ rfl)
    (isMultiHomog_chartMon c 0) (hc 0), chartMon_zero, recR_one]
  have h : logNorm (constLine (ι := ι) M hM) 1 = fun _ ↦ -Real.log M := by
    funext z
    simp [logNorm, constLine, Real.log_inv]
  have hfin : Finite (projPts W) := by
    rw [degC_eq_card_projPts] at hdeg
    exact (Nat.card_pos_iff.mp hdeg).2
  have key : ∀ φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ, ptsIntegral W φ (fun _ ↦ (1 : ℝ)) = degC W := by
    intro φ
    obtain rfl : φ = Fin.elim0 := funext fun j ↦ j.elim0
    rw [PtsIntegralPoints.homogProof K ι W (fun _ ↦ 1) hH hfin (fun _ _ _ _ ↦ rfl),
      degC_eq_card_projPts]
    have := Fintype.ofFinite (projPts W)
    rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.card_eq_fintype_card]
  unfold arInt
  rw [h, Inter.Conservation.ptsIntegral_const, key]
  ring

end Curve

section Point

def ptIdeal : Ideal (MRing (PBlk 2)) := orbitIdeal samplePoint

end Point

section Shift


end Shift

section Main

end Main

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
