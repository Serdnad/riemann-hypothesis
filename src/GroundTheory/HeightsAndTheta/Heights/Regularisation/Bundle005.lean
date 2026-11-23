module

public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
import Aesop.Main
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
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.RegularityCompacts
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMollA
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMollB
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology MeasureTheory Set
open ReciprocityTheory.AnForm.A (IsPsh Mollifier molli coordDiv limsupExt polyMax shrink)

noncomputable section

theorem trunc_ge_of_bdd {D : ℕ} {X : Type*} [TopologicalSpace X] {A : ReciprocityTheory.AnForm.M.FinHolAtlas D X}
    (R : RegChartData A) (K B : ℝ) (j : Fin R.N) {V : Set (Fin D → ℂ)} (hVo : IsOpen V)
    (hVt : V ⊆ (R.chart j).target) (hb : ∀ y ∈ V, R.trunc K j y ≤ B) {y : Fin D → ℂ} (hy : y ∈ V) :
    -K ≤ R.trunc K j y := by
  unfold RegChartData.trunc limsupExt
  split_ifs with hA
  · have := ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.nebot_diff (S := R.S j) (R.chart j).open_target (hVt hy)
    have hbdd : IsBoundedUnder (· ≤ ·) (𝓝[(R.chart j).target \ coordDiv (R.S j)] y)
        (fun y => max (R.u j y) (-K)) := by
      refine isBoundedUnder_of_eventually_le (a := B) ?_
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hVo.mem_nhds hy), self_mem_nhdsWithin]
        with y' hy'V hy'
      have h := hb y' hy'V
      simp only [RegChartData.trunc, limsupExt, if_neg hy'.2] at h
      exact h
    refine le_limsup_of_le hbdd (fun b hb' => ?_)
    obtain ⟨y', hy'⟩ := hb'.exists
    exact (le_max_right _ _).trans hy'
  · exact le_max_right (R.u j y) (-K)

theorem le_molli_of_ge {D : ℕ} (ρ : Mollifier D) {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ}
    (hU : IsOpen U) (hφ : IsPsh U φ) {t c : ℝ} (ht : 0 < t) {z : Fin D → ℂ}
    (hz : closedBall z t ⊆ U) (hc : ∀ y ∈ closedBall z t, c ≤ φ y) : c ≤ molli ρ t φ z := by
  obtain ⟨-, hi⟩ := ReciprocityTheory.AnForm.A.phiC hU hφ (isCompact_closedBall z t) hz
  rw [ReciprocityTheory.AnForm.A.molli_eq_C ρ ht (subset_refl _)]
  calc c = ∫ y, ρ.scaled t y * c := by
        rw [integral_mul_const, ReciprocityTheory.AnForm.A.integral_scaled ρ ht, one_mul]
    _ ≤ _ := by
      refine integral_mono ((ReciprocityTheory.AnForm.A.integrable_scaled ρ ht).mul_const _)
        (ReciprocityTheory.AnForm.A.integrable_kC ρ ht hi z) fun y => ?_
      by_cases hy : ρ.scaled t y = 0
      · simp [hy]
      refine mul_le_mul_of_nonneg_left ?_ (ReciprocityTheory.AnForm.A.scaled_nonneg ρ ht y)
      have hmem := ReciprocityTheory.AnForm.A.mem_ball_sub ρ ht hy z
      rw [indicator_of_mem hmem]
      exact hc _ hmem

theorem ChartMollifiedBounds.proof (h : TruncPsh.Statement) : ChartMollifiedBounds.Statement := by
  intro X _ _ _ D A R ρ
  obtain ⟨δ, B, hδ, hV⟩ := h X D A R
  choose V hVo hVt hVball hVpsh using hV

  have hcpt : ∀ j, IsCompact (R.chart j '' closure (R.mid j)) := fun j =>
    isClosed_closure.isCompact.image_of_continuousOn
      ((R.chart j).continuousOn.mono (R.closure_mid j))
  have himg : ∀ j, R.chart j '' closure (R.mid j) ⊆ (R.chart j).target := by
    rintro j _ ⟨x, hx, rfl⟩
    exact (R.chart j).map_source (R.closure_mid j hx)
  choose r hr hrt using fun j => (hcpt j).exists_cthickening_subset_open (R.chart j).open_target (himg j)

  obtain ⟨ε, hε, hεr⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ j, ε ≤ r j := by
    rcases isEmpty_or_nonempty (Fin R.N) with hN | hN
    · exact ⟨1, one_pos, fun j => (IsEmpty.false j).elim⟩
    · obtain ⟨j₀, -, hj₀⟩ := Finset.univ.exists_min_image r Finset.univ_nonempty
      exact ⟨r j₀, hr j₀, fun j => hj₀ j (Finset.mem_univ j)⟩

  choose Cq hCq using fun j => (hcpt j).exists_bound_of_continuousOn
    (((R.q_smooth j).continuousOn).mono (himg j))
  refine ⟨max B 0 + ∑ j, |Cq j|, min δ ε, lt_min hδ hε, fun t ht ht₀ => ⟨?_, ?_⟩⟩
  · intro j x hx
    exact (closedBall_subset_cthickening (mem_image_of_mem _ hx) t).trans
      ((cthickening_mono ((ht₀.trans_le (min_le_right _ _)).le.trans (hεr j)) _).trans (hrt j))
  intro K hK j x hx
  have hxs : x ∈ (R.chart j).source := R.closure_mid j (subset_closure hx)
  obtain ⟨hpsh, hbd⟩ := hVpsh j K
  have htδ : t ≤ δ := (ht₀.trans_le (min_le_left _ _)).le
  have hball : closedBall (R.chart j x) t ⊆ V j :=
    (closedBall_subset_closedBall htδ).trans (hVball j x hx)
  have hq : |R.q j (R.chart j x)| ≤ ∑ j, |Cq j| := by
    have h1 := hCq j (R.chart j x) (mem_image_of_mem _ (subset_closure hx))
    rw [Real.norm_eq_abs] at h1
    exact h1.trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun j => |Cq j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)))

  have hlow : -K ≤ molli ρ t (R.trunc K j) (R.chart j x) :=
    le_molli_of_ge ρ (hVo j) hpsh ht hball fun y hy =>
      trunc_ge_of_bdd R K _ j (hVo j) (hVt j) hbd (hball hy)
  have hup : molli ρ t (R.trunc K j) (R.chart j x) ≤ max B 0 := by
    have h1 := ReciprocityTheory.AnForm.A.molli_le_polyMax ρ (hVo j) hpsh ht (z := R.chart j x) hball
    refine h1.trans (ReciprocityTheory.AnForm.A.polyMax_le' ht.le fun y hy => ?_)
    exact (hbd y (hball hy)).trans (max_le_max le_rfl (by linarith))
  have hphReg : R.phReg ρ K t j x = molli ρ t (R.trunc K j) (R.chart j x) - R.q j (R.chart j x) := rfl
  refine ⟨?_, ?_, fun hY => ?_⟩
  · rw [hphReg]; linarith [neg_abs_le (R.q j (R.chart j x)), le_abs_self (R.q j (R.chart j x)), le_max_right B 0]
  · rw [hphReg]; linarith [neg_abs_le (R.q j (R.chart j x)), le_abs_self (R.q j (R.chart j x)), le_max_right B 0]
  ·
    have hA : R.chart j x ∉ coordDiv (R.S j) := (R.mem_Yo j x hxs).1 hY
    have htr : R.trunc K j (R.chart j x) = max (R.u j (R.chart j x)) (-K) := by
      simp only [RegChartData.trunc, limsupExt, if_neg hA]
    have hu : R.u j (R.chart j x) = R.q j (R.chart j x) + R.ph x := by
      simp only [RegChartData.u, PotentialCharts.chartFun, (R.chart j).left_inv hxs]
    have hle := ReciprocityTheory.AnForm.A.le_molli ρ (hVo j) hpsh ht (z := R.chart j x) hball
    rw [hphReg]
    linarith [le_max_left (R.u j (R.chart j x)) (-K)]

end

end GroundTheory.Heights₂.Heights.Regular
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric
open ReciprocityTheory.AnForm.A (polyMax molli mollify_thm polyMax_le' polyMax_mono')

noncomputable section

theorem log_inv_facts {t a : ℝ} (ht : 0 < t) (ha : 0 ≤ a)
    (hta : t < Real.exp (-(Real.exp 1 + 2 * a))) :
    Real.exp 1 + 2 * a < Real.log t⁻¹ ∧ 1 < Real.log (Real.log t⁻¹) := by
  have h1 : Real.log t < -(Real.exp 1 + 2 * a) := by
    have := Real.log_lt_log ht hta
    rwa [Real.log_exp] at this
  rw [Real.log_inv]
  have he := Real.exp_pos 1
  refine ⟨by linarith, ?_⟩
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  linarith

theorem ChartComparison.proof (h0 : MollifiedLowerBound.Statement)
    (h1 : PolyMaxOscillation.Statement) (h2 : PolyMaxLowerBound.Statement)
    (h3 : TruncPsh.Statement) (h4 : TruncTransfer.Statement) : ChartComparison.Statement := by
  intro X _ _ _ D A R ρ
  obtain ⟨δ, B₀, hδ, hV⟩ := h3 X D A R
  choose V hVo _hVt hVball hVpsh using hV
  obtain ⟨δ₁, L, B₁, hδ₁, hL, hT⟩ := h4 X D A R
  obtain ⟨C₂, t₂, ht₂, hlow⟩ := h2 X D A R
  obtain ⟨b, hb⟩ := mollifier_exists_bound ρ
  have hb0 : 0 ≤ b := (ρ.nonneg 0).trans (hb 0)
  obtain ⟨c₀, hc₀⟩ : ∃ c : ℝ, c = Real.pi ^ D * (3 / 2 : ℝ) ^ (2 * D) * b := ⟨_, rfl⟩
  have hc₀0 : 0 ≤ c₀ := by rw [hc₀]; positivity
  obtain ⟨C₁, hC₁⟩ : ∃ c : ℝ, c = L + 2 := ⟨_, rfl⟩
  have hC₁3 : 3 ≤ C₁ := by linarith
  obtain ⟨a, ha⟩ : ∃ c : ℝ, c = |Real.log (δ / C₁)| := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := ha ▸ abs_nonneg _
  obtain ⟨B₀', hB₀'⟩ : ∃ c : ℝ, c = max B₀ 0 := ⟨_, rfl⟩
  obtain ⟨C₂', hC₂'⟩ : ∃ c : ℝ, c = max C₂ 0 := ⟨_, rfl⟩
  have hB₀'0 : 0 ≤ B₀' := hB₀' ▸ le_max_right _ _
  have hC₂'0 : 0 ≤ C₂' := hC₂' ▸ le_max_right _ _
  have hC₂C₂' : C₂ ≤ C₂' := hC₂' ▸ le_max_left _ _
  have hlog4 : 0 ≤ Real.log (4 * C₁ ^ 2) := Real.log_nonneg (by nlinarith)
  obtain ⟨E, hE⟩ : ∃ c : ℝ, c = (1 + c₀) * (2 * Real.log (4 * C₁ ^ 2) * (B₀' + C₂')) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ c : ℝ, c = max (max E L) (C₂' + |B₁| + 1) := ⟨_, rfl⟩
  have hCE : E ≤ C := hC ▸ (le_max_left _ _).trans (le_max_left _ _)
  have hCL : L ≤ C := hC ▸ (le_max_right _ _).trans (le_max_left _ _)
  have hCB : C₂' + |B₁| + 1 ≤ C := hC ▸ le_max_right _ _
  have hC0 : 0 ≤ C := by linarith [abs_nonneg B₁]
  have hC₁2 : 0 < C₁ + 2 := by linarith
  refine ⟨C, min (min t₂ δ₁) (min (δ / (C₁ + 2)) (Real.exp (-(Real.exp 1 + 2 * a)))),
    lt_min (lt_min ht₂ hδ₁) (lt_min (div_pos hδ hC₁2) (Real.exp_pos _)), ?_⟩
  intro t ht ht₀ K hK
  simp only [lt_min_iff] at ht₀
  obtain ⟨⟨htt₂, htδ₁⟩, htδ, hte⟩ := ht₀
  have hCt : t * (C₁ + 2) < δ := (lt_div_iff₀ hC₁2).1 htδ
  have hC₁t : C₁ * t ≤ δ := by linarith
  have hC₁tlt : C₁ * t < δ := by linarith
  have htLt : t ≤ L * t := le_mul_of_one_le_left ht.le hL
  have hLt : L * t ≤ C₁ * t := mul_le_mul_of_nonneg_right (by linarith) ht.le
  have h2t : 2 * t ≤ C₁ * t := mul_le_mul_of_nonneg_right (by linarith) ht.le
  have htC : t ≤ C₁ * t := le_mul_of_one_le_left ht.le (by linarith)
  obtain ⟨hℓa, hlogℓ⟩ := log_inv_facts ht ha0 hte
  have hℓ0 : 0 < Real.log t⁻¹ := by linarith [Real.exp_pos 1]
  have hK0 : 0 ≤ K := le_trans (mul_nonneg hC0 (by linarith)) hK
  have hKB : -K + B₁ ≤ -C₂ * Real.log (Real.log t⁻¹) := by
    have h1' : (C₂' + |B₁| + 1) * Real.log (Real.log t⁻¹) ≤ C * Real.log (Real.log t⁻¹) :=
      mul_le_mul_of_nonneg_right hCB (by linarith)
    have h2' : B₁ ≤ |B₁| * Real.log (Real.log t⁻¹) := by
      have := le_mul_of_one_le_right (abs_nonneg B₁) hlogℓ.le
      linarith [le_abs_self B₁]
    have h3' : C₂ * Real.log (Real.log t⁻¹) ≤ C₂' * Real.log (Real.log t⁻¹) :=
      mul_le_mul_of_nonneg_right hC₂C₂' (by linarith)
    linarith
  have key : ∀ j k : Fin R.N, ∀ x ∈ R.mid j ∩ R.mid k,
      R.phReg ρ K t j x - R.phReg ρ K t k x ≤ E * (Real.log (Real.log t⁻¹) / Real.log t⁻¹) + L * t := by
    intro j k x hx
    obtain ⟨hpj, -⟩ := hVpsh j K
    obtain ⟨hpk, hbk⟩ := hVpsh k K
    have hball : ∀ r, r ≤ δ → closedBall (R.chart k x) r ⊆ V k := fun r hr =>
      (closedBall_subset_closedBall hr).trans (hVball k x hx.2)
    have hballj : closedBall (R.chart j x) t ⊆ V j :=
      (closedBall_subset_closedBall (by linarith : t ≤ δ)).trans (hVball j x hx.1)

    have hi : molli ρ t (R.trunc K j) (R.chart j x) ≤ polyMax (R.trunc K j) (R.chart j x) t :=
      (((mollify_thm D ρ (V j) (R.trunc K j) (hVo j) hpj).1 t ht).2.2.2 (R.chart j x) hballj).2

    have hii : polyMax (R.trunc K j) (R.chart j x) t ≤
        max (polyMax (R.trunc K k) (R.chart k x) (L * t)) (-K + B₁) +
          (R.q j (R.chart j x) - R.q k (R.chart k x)) + L * t :=
      polyMax_le' ht.le fun y hy => hT K j k x hx t ht htδ₁ y hy
    have mono : ∀ s s', 0 ≤ s → s ≤ s' → s' ≤ δ →
        polyMax (R.trunc K k) (R.chart k x) s ≤ polyMax (R.trunc K k) (R.chart k x) s' :=
      fun s s' hs hss' hs' => polyMax_mono' hpk.1 hs hss' (hball _ hs')
    have hlowk := hlow t ht htt₂ K k x hx.2
    have e0 := mono t (L * t) ht.le htLt (by linarith)
    have e1 := mono (L * t) (C₁ * t) (by linarith) hLt hC₁t
    have hq : t / (4 * C₁) ≤ t / 4 := div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith)
    have e2 := mono (t / (4 * C₁)) (t / 4) (by positivity) hq (by linarith)
    have e3 := mono (t / 4) (2 * t) (by positivity) (by linarith) (by linarith)
    have e4 := mono (2 * t) (C₁ * t) (by positivity) h2t hC₁t
    have hmax : max (polyMax (R.trunc K k) (R.chart k x) (L * t)) (-K + B₁) =
        polyMax (R.trunc K k) (R.chart k x) (L * t) := max_eq_left (by linarith)
    rw [hmax] at hii

    have hiv := h0 D ρ b (V k) (R.trunc K k) (R.chart k x) t (hVo k) hpk ht
      (hball _ (by linarith)) hb
    rw [← hc₀] at hiv

    have hv := h1 D (V k) (R.trunc K k) (R.chart k x) δ t C₁ (hVo k) hpk (hball δ le_rfl) ht
      (by linarith) hC₁tlt
    have hMδ : polyMax (R.trunc K k) (R.chart k x) δ ≤ B₀' :=
      polyMax_le' hδ.le fun y hy => (hbk y (hVball k x hx.2 hy)).trans
        (max_le (hB₀' ▸ le_max_left _ _) (by linarith))
    have hN : polyMax (R.trunc K k) (R.chart k x) δ - polyMax (R.trunc K k) (R.chart k x) (C₁ * t) ≤
        (B₀' + C₂') * Real.log (Real.log t⁻¹) := by
      have h1' : C₂ * Real.log (Real.log t⁻¹) ≤ C₂' * Real.log (Real.log t⁻¹) :=
        mul_le_mul_of_nonneg_right hC₂C₂' (by linarith)
      have h2' : B₀' ≤ B₀' * Real.log (Real.log t⁻¹) := le_mul_of_one_le_right hB₀'0 hlogℓ.le
      have h3' : -C₂ * Real.log (Real.log t⁻¹) = -(C₂ * Real.log (Real.log t⁻¹)) := by ring
      linarith
    have hden : Real.log t⁻¹ / 2 ≤ Real.log (δ / (C₁ * t)) := by
      rw [show δ / (C₁ * t) = (δ / C₁) * t⁻¹ by field_simp,
        Real.log_mul (div_pos hδ (by linarith)).ne' (inv_pos.2 ht).ne']
      have := neg_abs_le (Real.log (δ / C₁))
      rw [← ha] at this
      linarith [Real.exp_pos 1]
    have hden0 : 0 < Real.log (δ / (C₁ * t)) := by linarith
    have hP : 0 ≤ 2 * Real.log (4 * C₁ ^ 2) * (B₀' + C₂') := by positivity
    have hO : polyMax (R.trunc K k) (R.chart k x) (C₁ * t) -
          polyMax (R.trunc K k) (R.chart k x) (t / (4 * C₁)) ≤
        2 * Real.log (4 * C₁ ^ 2) * (B₀' + C₂') * (Real.log (Real.log t⁻¹) / Real.log t⁻¹) := by
      refine hv.trans ?_
      rw [div_le_iff₀ hden0]
      calc Real.log (4 * C₁ ^ 2) * (polyMax (R.trunc K k) (R.chart k x) δ -
              polyMax (R.trunc K k) (R.chart k x) (C₁ * t))
          ≤ Real.log (4 * C₁ ^ 2) * ((B₀' + C₂') * Real.log (Real.log t⁻¹)) :=
            mul_le_mul_of_nonneg_left hN hlog4
        _ = 2 * Real.log (4 * C₁ ^ 2) * (B₀' + C₂') *
              (Real.log (Real.log t⁻¹) / Real.log t⁻¹) * (Real.log t⁻¹ / 2) := by
            have hx := div_mul_cancel₀ (Real.log (Real.log t⁻¹)) hℓ0.ne'
            linear_combination (-(Real.log (4 * C₁ ^ 2) * (B₀' + C₂'))) * hx
        _ ≤ 2 * Real.log (4 * C₁ ^ 2) * (B₀' + C₂') *
              (Real.log (Real.log t⁻¹) / Real.log t⁻¹) * Real.log (δ / (C₁ * t)) :=
            mul_le_mul_of_nonneg_left hden (mul_nonneg hP (div_nonneg (by linarith) hℓ0.le))
    have hc : c₀ * (polyMax (R.trunc K k) (R.chart k x) (2 * t) -
          polyMax (R.trunc K k) (R.chart k x) (t / 4)) ≤
        c₀ * (polyMax (R.trunc K k) (R.chart k x) (C₁ * t) -
          polyMax (R.trunc K k) (R.chart k x) (t / (4 * C₁))) :=
      mul_le_mul_of_nonneg_left (by linarith) hc₀0
    have hfin : (1 + c₀) * (polyMax (R.trunc K k) (R.chart k x) (C₁ * t) -
          polyMax (R.trunc K k) (R.chart k x) (t / (4 * C₁))) ≤
        E * (Real.log (Real.log t⁻¹) / Real.log t⁻¹) := by
      rw [hE]
      have := mul_le_mul_of_nonneg_left hO (by linarith : (0 : ℝ) ≤ 1 + c₀)
      linarith
    simp only [RegChartData.phReg, RegChartData.smoothed]
    linarith
  have hr : 0 ≤ Real.log (Real.log t⁻¹) / Real.log t⁻¹ := div_nonneg (by linarith) hℓ0.le
  intro j k x hx
  have hEC : E * (Real.log (Real.log t⁻¹) / Real.log t⁻¹) + L * t ≤
      C * Real.log (Real.log t⁻¹) / Real.log t⁻¹ + C * t := by
    rw [mul_div_assoc]
    have := mul_le_mul_of_nonneg_right hCE hr
    have := mul_le_mul_of_nonneg_right hCL ht.le
    linarith
  exact abs_sub_le_iff.2 ⟨(key j k x hx).trans hEC, (key k j x ⟨hx.2, hx.1⟩).trans hEC⟩

end

end GroundTheory.Heights₂.Heights.Regular
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open MeasureTheory Metric Set
open ReciprocityTheory.AnForm.A

noncomputable section

theorem volume_real_closedBall_polydisc {D : ℕ} (x : Fin D → ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (closedBall x r) = (Real.pi * r ^ 2) ^ D := by
  rw [Measure.real, volume_pi_closedBall x hr]
  simp only [Complex.volume_closedBall, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr]
  simp [mul_comm]

theorem MollifiedLowerBound.proof (h0 : SubMeanPolydiscStatement)
    (h1 : PolyMaxLogConvexStatement) : MollifiedLowerBound.Statement := by
  intro D ρ b U u z t hU hu ht hzU hb
  set M2 := polyMax u z (2 * t)
  set M4 := polyMax u z (t / 4)
  obtain ⟨-, -, hatt, -⟩ := h1 D U u z (2 * t) hU hu (by positivity) hzU
  obtain ⟨x, hx, hux⟩ := hatt (t / 4) (by positivity) (by linarith)
  rw [mem_closedBall] at hx
  set B := closedBall x (3 / 2 * t) with hBdef
  have hBz : B ⊆ closedBall z (2 * t) :=
    closedBall_subset_closedBall' (by linarith)
  have hzB : closedBall z t ⊆ B :=
    closedBall_subset_closedBall' (by rw [dist_comm]; linarith)
  obtain ⟨hint, hmean⟩ := h0 D U u x (3 / 2 * t) hU hu (by positivity) (hBz.trans hzU)
  rw [← hBdef] at hint hmean
  have hle2 : ∀ p ∈ B, u p ≤ M2 := fun p hp => le_polyMax hu.1 hzU (hBz hp)
  have hb0 : 0 ≤ b := (ρ.nonneg 0).trans (hb 0)
  have hV : volume.real B = (Real.pi * (3 / 2 * t) ^ 2) ^ D :=
    volume_real_closedBall_polydisc x (by positivity)
  have hVpos : 0 < volume.real B := by rw [hV]; positivity
  have hcint : IntegrableOn (fun _ => M2) B := integrableOn_const measure_closedBall_lt_top.ne

  have hIB : ∫ p in B, (M2 - u p) ≤ volume.real B * (M2 - M4) := by
    rw [integral_sub hcint hint, setIntegral_const, smul_eq_mul]
    rw [setAverage_eq, smul_eq_mul] at hmean
    have h := mul_le_mul_of_nonneg_left hmean hVpos.le
    rw [← mul_assoc, mul_inv_cancel₀ hVpos.ne', one_mul] at h
    rw [show M4 = u x from hux.symm]
    linarith

  set g : (Fin D → ℂ) → ℝ := B.indicator (fun p => M2 - u p) with hgdef
  have hg0 : ∀ q, 0 ≤ g q := by
    intro q
    by_cases hq : q ∈ B
    · rw [hgdef, indicator_of_mem hq]; exact sub_nonneg.2 (hle2 q hq)
    · rw [hgdef, indicator_of_notMem hq]
  have hgint : Integrable g :=
    (integrable_indicator_iff measurableSet_closedBall).2 (hcint.sub hint)
  have hBind : Integrable (B.indicator u) :=
    (integrable_indicator_iff measurableSet_closedBall).2 hint
  set c : ℝ := (t ^ (2 * D))⁻¹ * b with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hsc : ∀ y, ρ.scaled t y ≤ c := fun y =>
    mul_le_mul_of_nonneg_left (hb _) (by positivity)
  have key : ∫ y, (ρ.scaled t y * M2 - ρ.scaled t y * B.indicator u (z - y)) ≤
      ∫ y, c * g (z - y) := by
    refine integral_mono (((integrable_scaled ρ ht).mul_const M2).sub
      (integrable_kC ρ ht hBind z)) ((hgint.comp_sub_left z).const_mul c) fun y => ?_
    by_cases hy : ρ.scaled t y = 0
    · simp only [hy, zero_mul, sub_zero]
      exact mul_nonneg hc0 (hg0 _)
    · have hm : z - y ∈ B := hzB (mem_ball_sub ρ ht hy z)
      simp only [hgdef, indicator_of_mem hm]
      rw [← mul_sub]
      exact mul_le_mul_of_nonneg_right (hsc y) (sub_nonneg.2 (hle2 _ hm))
  have hLHS : ∫ y, (ρ.scaled t y * M2 - ρ.scaled t y * B.indicator u (z - y)) =
      M2 - molli ρ t u z := by
    rw [integral_sub ((integrable_scaled ρ ht).mul_const M2) (integrable_kC ρ ht hBind z),
      integral_mul_const, integral_scaled ρ ht, one_mul, molli_eq_C ρ ht hzB (φ := u)]
  have hRHS : ∫ y, c * g (z - y) = c * ∫ p in B, (M2 - u p) := by
    rw [integral_const_mul]
    congr 1
    have := (Measure.measurePreserving_sub_left volume z).integral_comp
      (Homeomorph.subLeft z).measurableEmbedding g
    rw [this, hgdef, integral_indicator measurableSet_closedBall]
  have hcV : c * volume.real B = Real.pi ^ D * (3 / 2 : ℝ) ^ (2 * D) * b := by
    rw [hV, hcdef]
    have ht' : t ^ (2 * D) ≠ 0 := by positivity
    rw [mul_pow, ← pow_mul, mul_pow, pow_mul (3 / 2 : ℝ) 2 D]
    field_simp
  have hfin := mul_le_mul_of_nonneg_left hIB hc0
  have e : c * (volume.real B * (M2 - M4)) =
      Real.pi ^ D * (3 / 2 : ℝ) ^ (2 * D) * b * (M2 - M4) := by
    rw [← hcV]; ring
  linarith

theorem MollifiedLowerBound.closed : MollifiedLowerBound.Statement :=
  MollifiedLowerBound.proof subMeanPolydisc_thm polyMaxLogConvex_thm

end

end GroundTheory.Heights₂.Heights.Regular
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric

noncomputable section

theorem PolyMaxOscillation.proof (h0 : ReciprocityTheory.AnForm.A.PolyMaxLogConvexStatement) :
    PolyMaxOscillation.Statement := by
  intro D U u z δ t C₁ hU hu hδ ht hC hCt
  have hC0 : 0 < C₁ := by linarith
  have hb0 : 0 < C₁ * t := mul_pos hC0 ht
  have hδ0 : 0 < δ := hb0.trans hCt
  have hconv := (h0 D U u z δ hU hu hδ0 hδ).1
  have ha0 : 0 < t / (4 * C₁) := by positivity
  have hab : t / (4 * C₁) < C₁ * t := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have key := hconv.slope_mono_adjacent
    (Set.mem_Iic.2 (Real.log_le_log ha0 (hab.trans hCt).le)) (Set.mem_Iic.2 le_rfl)
    (Real.log_lt_log ha0 hab) (Real.log_lt_log hb0 hCt)
  simp only [Real.exp_log ha0, Real.exp_log hb0, Real.exp_log hδ0] at key
  have h1 : Real.log (C₁ * t) - Real.log (t / (4 * C₁)) = Real.log (4 * C₁ ^ 2) := by
    rw [← Real.log_div hb0.ne' ha0.ne']
    congr 1
    field_simp
  have h2 : Real.log δ - Real.log (C₁ * t) = Real.log (δ / (C₁ * t)) :=
    (Real.log_div hδ0.ne' hb0.ne').symm
  have hL1 : 0 < Real.log (4 * C₁ ^ 2) := by
    rw [← h1]
    exact sub_pos.2 (Real.log_lt_log ha0 hab)
  rw [h1, h2, div_le_iff₀ hL1] at key
  rw [mul_div_assoc, mul_comm (Real.log (4 * C₁ ^ 2))]
  exact key

theorem PolyMaxOscillation.proof_closed : PolyMaxOscillation.Statement :=
  PolyMaxOscillation.proof ReciprocityTheory.AnForm.A.polyMaxLogConvex_thm

end

end GroundTheory.Heights₂.Heights.Regular
end
